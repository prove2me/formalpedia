-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1720_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:59:04.38635+00:00
-- url     : https://prove2.me/submissions/4831f009-7339-4a3e-84d6-f743926ac790

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
theorem support_rectangle_w1720_s3_0 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-344187819/2500000000 : ℝ)*x 0 + (2731856489/5000000000 : ℝ)*x 1 + (1284858193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344187819/2500000000 : ℝ)^5383 ≤ (1080111644209/12500000000000 : ℝ)^4359 := by
    have hnat : (344187819 : ℕ)^5383*12500000000000^4359 ≤ 1080111644209^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344187819 2500000000 1080111644209 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731856489/5000000000 : ℝ)^5383 ≤ (23702246668971/50000000000000 : ℝ)^4359 := by
    have hnat : (2731856489 : ℕ)^5383*50000000000000^4359 ≤ 23702246668971^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731856489 5000000000 23702246668971 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284858193/2500000000 : ℝ)^5383 ≤ (43954613491/100000000000 : ℝ)^4359 := by
    have hnat : (1284858193 : ℕ)^5383*100000000000^4359 ≤ 43954613491^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284858193 2500000000 43954613491 100000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-344187819/2500000000 : ℝ), (2731856489/5000000000 : ℝ), (1284858193/2500000000 : ℝ)] ![(1080111644209/12500000000000 : ℝ), (23702246668971/50000000000000 : ℝ), (43954613491/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-344187819/2500000000 : ℝ)|^5383 ≤ (1080111644209/12500000000000 : ℝ)^4359
        have hw : |(-344187819/2500000000 : ℝ)|=(344187819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731856489/5000000000 : ℝ)|^5383 ≤ (23702246668971/50000000000000 : ℝ)^4359
        have hw : |(2731856489/5000000000 : ℝ)|=(2731856489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284858193/2500000000 : ℝ)|^5383 ≤ (43954613491/100000000000 : ℝ)^4359
        have hw : |(1284858193/2500000000 : ℝ)|=(1284858193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s3_1 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670077327/5000000000 : ℝ)*x 0 + (-1544762747/10000000000 : ℝ)*x 1 + (642429101/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670077327/5000000000 : ℝ)^5383 ≤ (4608417307423/10000000000000 : ℝ)^4359 := by
    have hnat : (2670077327 : ℕ)^5383*10000000000000^4359 ≤ 4608417307423^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670077327 5000000000 4608417307423 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1544762747/10000000000 : ℝ)^5383 ≤ (9961213034029/100000000000000 : ℝ)^4359 := by
    have hnat : (1544762747 : ℕ)^5383*100000000000000^4359 ≤ 9961213034029^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544762747 10000000000 9961213034029 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642429101/1250000000 : ℝ)^5383 ≤ (8790922774243/20000000000000 : ℝ)^4359 := by
    have hnat : (642429101 : ℕ)^5383*20000000000000^4359 ≤ 8790922774243^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642429101 1250000000 8790922774243 20000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670077327/5000000000 : ℝ), (-1544762747/10000000000 : ℝ), (642429101/1250000000 : ℝ)] ![(4608417307423/10000000000000 : ℝ), (9961213034029/100000000000000 : ℝ), (8790922774243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670077327/5000000000 : ℝ)|^5383 ≤ (4608417307423/10000000000000 : ℝ)^4359
        have hw : |(2670077327/5000000000 : ℝ)|=(2670077327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1544762747/10000000000 : ℝ)|^5383 ≤ (9961213034029/100000000000000 : ℝ)^4359
        have hw : |(-1544762747/10000000000 : ℝ)|=(1544762747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642429101/1250000000 : ℝ)|^5383 ≤ (8790922774243/20000000000000 : ℝ)^4359
        have hw : |(642429101/1250000000 : ℝ)|=(642429101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s3_2 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335038671/2500000000 : ℝ)*x 0 + (5139432783/10000000000 : ℝ)*x 1 + (-772381371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335038671/2500000000 : ℝ)^5383 ≤ (46084173393941/100000000000000 : ℝ)^4359 := by
    have hnat : (1335038671 : ℕ)^5383*100000000000000^4359 ≤ 46084173393941^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335038671 2500000000 46084173393941 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139432783/10000000000 : ℝ)^5383 ≤ (43954613607177/100000000000000 : ℝ)^4359 := by
    have hnat : (5139432783 : ℕ)^5383*100000000000000^4359 ≤ 43954613607177^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139432783 10000000000 43954613607177 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (772381371/5000000000 : ℝ)^5383 ≤ (9961212994213/100000000000000 : ℝ)^4359 := by
    have hnat : (772381371 : ℕ)^5383*100000000000000^4359 ≤ 9961212994213^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772381371 5000000000 9961212994213 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335038671/2500000000 : ℝ), (5139432783/10000000000 : ℝ), (-772381371/5000000000 : ℝ)] ![(46084173393941/100000000000000 : ℝ), (43954613607177/100000000000000 : ℝ), (9961212994213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335038671/2500000000 : ℝ)|^5383 ≤ (46084173393941/100000000000000 : ℝ)^4359
        have hw : |(1335038671/2500000000 : ℝ)|=(1335038671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139432783/10000000000 : ℝ)|^5383 ≤ (43954613607177/100000000000000 : ℝ)^4359
        have hw : |(5139432783/10000000000 : ℝ)|=(5139432783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-772381371/5000000000 : ℝ)|^5383 ≤ (9961212994213/100000000000000 : ℝ)^4359
        have hw : |(-772381371/5000000000 : ℝ)|=(772381371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s3_3 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1023018907/2500000000 : ℝ)*x 0 + (3628667507/10000000000 : ℝ)*x 1 + (1147576619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023018907/2500000000 : ℝ)^5383 ≤ (33172859055983/100000000000000 : ℝ)^4359 := by
    have hnat : (1023018907 : ℕ)^5383*100000000000000^4359 ≤ 33172859055983^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023018907 2500000000 33172859055983 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3628667507/10000000000 : ℝ)^5383 ≤ (3574659168729/12500000000000 : ℝ)^4359 := by
    have hnat : (3628667507 : ℕ)^5383*12500000000000^4359 ≤ 3574659168729^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3628667507 10000000000 3574659168729 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147576619/2500000000 : ℝ)^5383 ≤ (19114933784603/50000000000000 : ℝ)^4359 := by
    have hnat : (1147576619 : ℕ)^5383*50000000000000^4359 ≤ 19114933784603^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147576619 2500000000 19114933784603 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1023018907/2500000000 : ℝ), (3628667507/10000000000 : ℝ), (1147576619/2500000000 : ℝ)] ![(33172859055983/100000000000000 : ℝ), (3574659168729/12500000000000 : ℝ), (19114933784603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1023018907/2500000000 : ℝ)|^5383 ≤ (33172859055983/100000000000000 : ℝ)^4359
        have hw : |(1023018907/2500000000 : ℝ)|=(1023018907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3628667507/10000000000 : ℝ)|^5383 ≤ (3574659168729/12500000000000 : ℝ)^4359
        have hw : |(3628667507/10000000000 : ℝ)|=(3628667507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147576619/2500000000 : ℝ)|^5383 ≤ (19114933784603/50000000000000 : ℝ)^4359
        have hw : |(1147576619/2500000000 : ℝ)|=(1147576619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s3_4 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-275378921/2000000000 : ℝ)*x 0 + (160720467/312500000 : ℝ)*x 1 + (1365009557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275378921/2000000000 : ℝ)^5383 ≤ (1080250508331/12500000000000 : ℝ)^4359 := by
    have hnat : (275378921 : ℕ)^5383*12500000000000^4359 ≤ 1080250508331^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275378921 2000000000 1080250508331 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160720467/312500000 : ℝ)^5383 ≤ (21996436165571/50000000000000 : ℝ)^4359 := by
    have hnat : (160720467 : ℕ)^5383*50000000000000^4359 ≤ 21996436165571^4359*312500000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160720467 312500000 21996436165571 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365009557/2500000000 : ℝ)^5383 ≤ (47365123590787/100000000000000 : ℝ)^4359 := by
    have hnat : (1365009557 : ℕ)^5383*100000000000000^4359 ≤ 47365123590787^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365009557 2500000000 47365123590787 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275378921/2000000000 : ℝ), (160720467/312500000 : ℝ), (1365009557/2500000000 : ℝ)] ![(1080250508331/12500000000000 : ℝ), (21996436165571/50000000000000 : ℝ), (47365123590787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275378921/2000000000 : ℝ)|^5383 ≤ (1080250508331/12500000000000 : ℝ)^4359
        have hw : |(-275378921/2000000000 : ℝ)|=(275378921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160720467/312500000 : ℝ)|^5383 ≤ (21996436165571/50000000000000 : ℝ)^4359
        have hw : |(160720467/312500000 : ℝ)|=(160720467/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365009557/2500000000 : ℝ)|^5383 ≤ (47365123590787/100000000000000 : ℝ)^4359
        have hw : |(1365009557/2500000000 : ℝ)|=(1365009557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s3_5 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253349471/10000000000 : ℝ)*x 0 + (-1224160173/10000000000 : ℝ)*x 1 + (5460033843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253349471/10000000000 : ℝ)^5383 ≤ (4516086279481/10000000000000 : ℝ)^4359 := by
    have hnat : (5253349471 : ℕ)^5383*10000000000000^4359 ≤ 4516086279481^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253349471 10000000000 4516086279481 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1224160173/10000000000 : ℝ)^5383 ≤ (3737030288653/50000000000000 : ℝ)^4359 := by
    have hnat : (1224160173 : ℕ)^5383*50000000000000^4359 ≤ 3737030288653^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224160173 10000000000 3737030288653 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460033843/10000000000 : ℝ)^5383 ≤ (47365076615433/100000000000000 : ℝ)^4359 := by
    have hnat : (5460033843 : ℕ)^5383*100000000000000^4359 ≤ 47365076615433^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460033843 10000000000 47365076615433 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253349471/10000000000 : ℝ), (-1224160173/10000000000 : ℝ), (5460033843/10000000000 : ℝ)] ![(4516086279481/10000000000000 : ℝ), (3737030288653/50000000000000 : ℝ), (47365076615433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253349471/10000000000 : ℝ)|^5383 ≤ (4516086279481/10000000000000 : ℝ)^4359
        have hw : |(5253349471/10000000000 : ℝ)|=(5253349471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1224160173/10000000000 : ℝ)|^5383 ≤ (3737030288653/50000000000000 : ℝ)^4359
        have hw : |(-1224160173/10000000000 : ℝ)|=(1224160173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460033843/10000000000 : ℝ)|^5383 ≤ (47365076615433/100000000000000 : ℝ)^4359
        have hw : |(5460033843/10000000000 : ℝ)|=(5460033843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s3_6 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253349229/10000000000 : ℝ)*x 0 + (5460035653/10000000000 : ℝ)*x 1 + (-612078971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253349229/10000000000 : ℝ)^5383 ≤ (45160860225723/100000000000000 : ℝ)^4359 := by
    have hnat : (5253349229 : ℕ)^5383*100000000000000^4359 ≤ 45160860225723^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253349229 10000000000 45160860225723 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460035653/10000000000 : ℝ)^5383 ≤ (47365096005487/100000000000000 : ℝ)^4359 := by
    have hnat : (5460035653 : ℕ)^5383*100000000000000^4359 ≤ 47365096005487^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460035653 10000000000 47365096005487 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612078971/5000000000 : ℝ)^5383 ≤ (7474043756169/100000000000000 : ℝ)^4359 := by
    have hnat : (612078971 : ℕ)^5383*100000000000000^4359 ≤ 7474043756169^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612078971 5000000000 7474043756169 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253349229/10000000000 : ℝ), (5460035653/10000000000 : ℝ), (-612078971/5000000000 : ℝ)] ![(45160860225723/100000000000000 : ℝ), (47365096005487/100000000000000 : ℝ), (7474043756169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253349229/10000000000 : ℝ)|^5383 ≤ (45160860225723/100000000000000 : ℝ)^4359
        have hw : |(5253349229/10000000000 : ℝ)|=(5253349229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460035653/10000000000 : ℝ)|^5383 ≤ (47365096005487/100000000000000 : ℝ)^4359
        have hw : |(5460035653/10000000000 : ℝ)|=(5460035653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-612078971/5000000000 : ℝ)|^5383 ≤ (7474043756169/100000000000000 : ℝ)^4359
        have hw : |(-612078971/5000000000 : ℝ)|=(612078971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s3_7 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2046253657/5000000000 : ℝ)*x 0 + (2289781839/5000000000 : ℝ)*x 1 + (1819784619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046253657/5000000000 : ℝ)^5383 ≤ (265417445689/800000000000 : ℝ)^4359 := by
    have hnat : (2046253657 : ℕ)^5383*800000000000^4359 ≤ 265417445689^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046253657 5000000000 265417445689 800000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2289781839/5000000000 : ℝ)^5383 ≤ (38119409725601/100000000000000 : ℝ)^4359 := by
    have hnat : (2289781839 : ℕ)^5383*100000000000000^4359 ≤ 38119409725601^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289781839 5000000000 38119409725601 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1819784619/5000000000 : ℝ)^5383 ≤ (7175852387447/25000000000000 : ℝ)^4359 := by
    have hnat : (1819784619 : ℕ)^5383*25000000000000^4359 ≤ 7175852387447^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819784619 5000000000 7175852387447 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2046253657/5000000000 : ℝ), (2289781839/5000000000 : ℝ), (1819784619/5000000000 : ℝ)] ![(265417445689/800000000000 : ℝ), (38119409725601/100000000000000 : ℝ), (7175852387447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2046253657/5000000000 : ℝ)|^5383 ≤ (265417445689/800000000000 : ℝ)^4359
        have hw : |(2046253657/5000000000 : ℝ)|=(2046253657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2289781839/5000000000 : ℝ)|^5383 ≤ (38119409725601/100000000000000 : ℝ)^4359
        have hw : |(2289781839/5000000000 : ℝ)|=(2289781839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1819784619/5000000000 : ℝ)|^5383 ≤ (7175852387447/25000000000000 : ℝ)^4359
        have hw : |(1819784619/5000000000 : ℝ)|=(1819784619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1720_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/625 : ℝ)*pair X i i ≤ pair X i h) :
    (5043/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (63/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (63/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (63/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (63/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (63/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (63/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (63/625 : ℝ) ^ (5375/1024 : ℝ) ≤ (587680088833511/100000000000000000000 : ℝ) := by
    have hpowers : (63/625 : ℝ)^5375 ≤ (587680088833511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (63 : ℕ)^5375*100000000000000000000^1024 ≤ 587680088833511^1024*625^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63 625 587680088833511 100000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63/625 : ℝ)) (X := (587680088833511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17029/100000 : ℝ) ^ (5375/1024 : ℝ) ≤ (9214967452828901/100000000000000000000 : ℝ) := by
    have hpowers : (17029/100000 : ℝ)^5375 ≤ (9214967452828901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17029 : ℕ)^5375*100000000000000000000^1024 ≤ 9214967452828901^1024*100000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17029 100000 9214967452828901 100000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17029/100000 : ℝ)) (X := (9214967452828901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000587680088833511/50000000000000000000 : ℝ) ≤ (10000022391871561/10000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (50000587680088833511/50000000000000000000 : ℝ)^1024 ≤ (10000022391871561/10000000000000000 : ℝ)^5375 := by
      have hnat : (50000587680088833511 : ℕ)^1024*10000000000000000^5375 ≤ 10000022391871561^5375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000587680088833511 50000000000000000000 10000022391871561 10000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000022391871561/10000000000000000 : ℝ)) (X := (50000587680088833511/50000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002450661885415603/25000000000000000000 : ℝ) ≤ (2000037348885007/2000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (25002450661885415603/25000000000000000000 : ℝ)^1024 ≤ (2000037348885007/2000000000000000 : ℝ)^5375 := by
      have hnat : (25002450661885415603 : ℕ)^1024*2000000000000000^5375 ≤ 2000037348885007^5375*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002450661885415603 25000000000000000000 2000037348885007 2000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000037348885007/2000000000000000 : ℝ)) (X := (25002450661885415603/25000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009214967452828901/50000000000000000000 : ℝ) ≤ (10000351096978509/10000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (50009214967452828901/50000000000000000000 : ℝ)^1024 ≤ (10000351096978509/10000000000000000 : ℝ)^5375 := by
      have hnat : (50009214967452828901 : ℕ)^1024*10000000000000000^5375 ≤ 10000351096978509^5375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009214967452828901 50000000000000000000 10000351096978509 10000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000351096978509/10000000000000000 : ℝ)) (X := (50009214967452828901/50000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(587680088833511/100000000000000000000 : ℝ) ≤ ((69486842253637441549/69490000000000000000 : ℝ)+2*(82176276737/347450000000000 : ℝ)*(63/625 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (69486842253637441549/69490000000000000000 : ℝ)+2*(82176276737/347450000000000 : ℝ)*(63/625 : ℝ)=(10000022391871561/10000000000000000 : ℝ) by norm_num, show 1+2*(587680088833511/100000000000000000000 : ℝ)=(50000587680088833511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9214967452828901/100000000000000000000 : ℝ)+(587680088833511/100000000000000000000 : ℝ) ≤ ((69486842253637441549/69490000000000000000 : ℝ)+(82176276737/347450000000000 : ℝ)*((17029/100000 : ℝ)+(63/625 : ℝ)))^(5375/1024 : ℝ) := by
    rw [show (69486842253637441549/69490000000000000000 : ℝ)+(82176276737/347450000000000 : ℝ)*((17029/100000 : ℝ)+(63/625 : ℝ))=(2000037348885007/2000000000000000 : ℝ) by norm_num, show 1+(9214967452828901/100000000000000000000 : ℝ)+(587680088833511/100000000000000000000 : ℝ)=(25002450661885415603/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9214967452828901/100000000000000000000 : ℝ) ≤ ((69486842253637441549/69490000000000000000 : ℝ)+2*(82176276737/347450000000000 : ℝ)*(17029/100000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (69486842253637441549/69490000000000000000 : ℝ)+2*(82176276737/347450000000000 : ℝ)*(17029/100000 : ℝ)=(10000351096978509/10000000000000000 : ℝ) by norm_num, show 1+2*(9214967452828901/100000000000000000000 : ℝ)=(50009214967452828901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69486842253637441549/69490000000000000000 : ℝ)*(X 1 0+X 2 0)+(82176276737/347450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (63/625 : ℝ)) (hi := (17029/100000 : ℝ)) (c := (69486842253637441549/69490000000000000000 : ℝ)) (alpha := (82176276737/347450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69486842253637441549/69490000000000000000 : ℝ)*(X 0 1+X 2 1)+(82176276737/347450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (63/625 : ℝ)) (hi := (17029/100000 : ℝ)) (c := (69486842253637441549/69490000000000000000 : ℝ)) (alpha := (82176276737/347450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69486842253637441549/69490000000000000000 : ℝ)*(X 0 2+X 1 2)+(82176276737/347450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (63/625 : ℝ)) (hi := (17029/100000 : ℝ)) (c := (69486842253637441549/69490000000000000000 : ℝ)) (alpha := (82176276737/347450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-344187819/2500000000 : ℝ)*X 0 0+(2731856489/5000000000 : ℝ)*X 0 1+(1284858193/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670077327/5000000000 : ℝ)*X 1 0+(-1544762747/10000000000 : ℝ)*X 1 1+(642429101/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1335038671/2500000000 : ℝ)*X 2 0+(5139432783/10000000000 : ℝ)*X 2 1+(-772381371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1023018907/2500000000 : ℝ)*X 0 0+(3628667507/10000000000 : ℝ)*X 0 1+(1147576619/2500000000 : ℝ)*X 0 2+(1023018907/2500000000 : ℝ)*X 1 0+(3628667507/10000000000 : ℝ)*X 1 1+(1147576619/2500000000 : ℝ)*X 1 2+(1023018907/2500000000 : ℝ)*X 2 0+(3628667507/10000000000 : ℝ)*X 2 1+(1147576619/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-275378921/2000000000 : ℝ)*X 0 0+(160720467/312500000 : ℝ)*X 0 1+(1365009557/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253349471/10000000000 : ℝ)*X 1 0+(-1224160173/10000000000 : ℝ)*X 1 1+(5460033843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253349229/10000000000 : ℝ)*X 2 0+(5460035653/10000000000 : ℝ)*X 2 1+(-612078971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2046253657/5000000000 : ℝ)*X 0 0+(2289781839/5000000000 : ℝ)*X 0 1+(1819784619/5000000000 : ℝ)*X 0 2+(2046253657/5000000000 : ℝ)*X 1 0+(2289781839/5000000000 : ℝ)*X 1 1+(1819784619/5000000000 : ℝ)*X 1 2+(2046253657/5000000000 : ℝ)*X 2 0+(2289781839/5000000000 : ℝ)*X 2 1+(1819784619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43975815473330199213041164503/3474500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (911101469/50000000000000 : ℝ)*(base19) + (173481693/10000000000000 : ℝ)*(base23) + (11183369/20000000000000 : ℝ)*(lower2) + (300249559/100000000000000 : ℝ)*(upper3) + (232147717/100000000000000 : ℝ)*(upper5) + (128865454790301/6250000000000 : ℝ)*(major0) + (128865454790301/6250000000000 : ℝ)*(major1) + (2061847276644817/100000000000000 : ℝ)*(major2) + (1541885780783017/50000000000000 : ℝ)*(sp0) + (770947086555641/25000000000000 : ℝ)*(sp1) + (770947108402143/25000000000000 : ℝ)*(sp2) + (103989726543657/10000000000000 : ℝ)*(sp3) + (18606859469/100000000000000 : ℝ)*(sp4) + (1674384121/25000000000000 : ℝ)*(sp7) + (519951981486527/50000000000000 : ℝ)*(f.failure) + (1541895084212751/50000000000000 : ℝ)*(f.sum) + (39048344723347/17372500000000000000000000000 : ℝ)*base66 + (7276510815306896251/434312500000000000000000000000000 : ℝ)*base68 + (26498276611958298467/6949000000000000000000000000000000 : ℝ)*base70 + (4625493227259271251/434312500000000000000000000000000 : ℝ)*base72 + (154361965384809/34745000000000000000000000000 : ℝ)*base74 + (52529456676826298467/6949000000000000000000000000000000 : ℝ)*base76 + (4767210923593983751/434312500000000000000000000000000 : ℝ)*base78 + (4499311266248108751/434312500000000000000000000000000 : ℝ)*base80 + (11718713532097/4343125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (10464917/1000000000000000000000 : ℝ)*base89 + (10464917/1000000000000000000000 : ℝ)*base91 + (464917/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4854590948868383086769291223/868625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2222371049/100000000000000 : ℝ)*(base19) + (436976277/50000000000000 : ℝ)*(base23) + (70648661/10000000000000 : ℝ)*(lower2) + (109485051/50000000000000 : ℝ)*(lower3) + (6111401/25000000000000 : ℝ)*(lower4) + (527325254176597/25000000000000 : ℝ)*(major0) + (527325254176597/25000000000000 : ℝ)*(major1) + (527325254176597/25000000000000 : ℝ)*(major2) + (4848486493/100000000000000 : ℝ)*(sp0) + (1440431443/25000000000000 : ℝ)*(sp2) + (1577379741020517/50000000000000 : ℝ)*(sp4) + (1577381054078239/50000000000000 : ℝ)*(sp5) + (3154757694849201/100000000000000 : ℝ)*(sp6) + (531918758295579/50000000000000 : ℝ)*(sp7) + (531918758295579/50000000000000 : ℝ)*(f.failure) + (394345541315941/12500000000000 : ℝ)*(f.sum) + (5255943255141/17372500000000000000000000000 : ℝ)*base65 + (199137971527528753/1737250000000000000000000000000000 : ℝ)*base67 + (10440823331397028753/1737250000000000000000000000000000 : ℝ)*base69 + (1738141034571528753/1737250000000000000000000000000000 : ℝ)*base71 + (387900245781/17372500000000000000000000000 : ℝ)*base73 + (2811709750623528753/1737250000000000000000000000000000 : ℝ)*base75 + (4991299855293778753/1737250000000000000000000000000000 : ℝ)*base77 + (6097156481384778753/1737250000000000000000000000000000 : ℝ)*base79 + (27435180101801/17372500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3558391/1000000000000000000000 : ℝ)*base90 + (3558391/1000000000000000000000 : ℝ)*base92 + (3558391/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1720_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5043/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1720_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1720_s4_0 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-27535091/200000000 : ℝ)*x 0 + (5463702429/10000000000 : ℝ)*x 1 + (5139441071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27535091/200000000 : ℝ)^5383 ≤ (1728183705891/20000000000000 : ℝ)^4359 := by
    have hnat : (27535091 : ℕ)^5383*20000000000000^4359 ≤ 1728183705891^4359*200000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27535091 200000000 1728183705891 20000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463702429/10000000000 : ℝ)^5383 ≤ (47404380311427/100000000000000 : ℝ)^4359 := by
    have hnat : (5463702429 : ℕ)^5383*100000000000000^4359 ≤ 47404380311427^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463702429 10000000000 47404380311427 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139441071/10000000000 : ℝ)^5383 ≤ (5494337642643/12500000000000 : ℝ)^4359 := by
    have hnat : (5139441071 : ℕ)^5383*12500000000000^4359 ≤ 5494337642643^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139441071 10000000000 5494337642643 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27535091/200000000 : ℝ), (5463702429/10000000000 : ℝ), (5139441071/10000000000 : ℝ)] ![(1728183705891/20000000000000 : ℝ), (47404380311427/100000000000000 : ℝ), (5494337642643/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27535091/200000000 : ℝ)|^5383 ≤ (1728183705891/20000000000000 : ℝ)^4359
        have hw : |(-27535091/200000000 : ℝ)|=(27535091/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463702429/10000000000 : ℝ)|^5383 ≤ (47404380311427/100000000000000 : ℝ)^4359
        have hw : |(5463702429/10000000000 : ℝ)|=(5463702429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139441071/10000000000 : ℝ)|^5383 ≤ (5494337642643/12500000000000 : ℝ)^4359
        have hw : |(5139441071/10000000000 : ℝ)|=(5139441071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s4_1 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267007641/500000000 : ℝ)*x 0 + (-308950641/2000000000 : ℝ)*x 1 + (5139441853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267007641/500000000 : ℝ)^5383 ≤ (4608415352927/10000000000000 : ℝ)^4359 := by
    have hnat : (267007641 : ℕ)^5383*10000000000000^4359 ≤ 4608415352927^4359*500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267007641 500000000 4608415352927 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308950641/2000000000 : ℝ)^5383 ≤ (2490284262293/25000000000000 : ℝ)^4359 := by
    have hnat : (308950641 : ℕ)^5383*25000000000000^4359 ≤ 2490284262293^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308950641 2000000000 2490284262293 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139441853/10000000000 : ℝ)^5383 ≤ (43954709400263/100000000000000 : ℝ)^4359 := by
    have hnat : (5139441853 : ℕ)^5383*100000000000000^4359 ≤ 43954709400263^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139441853 10000000000 43954709400263 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267007641/500000000 : ℝ), (-308950641/2000000000 : ℝ), (5139441853/10000000000 : ℝ)] ![(4608415352927/10000000000000 : ℝ), (2490284262293/25000000000000 : ℝ), (43954709400263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267007641/500000000 : ℝ)|^5383 ≤ (4608415352927/10000000000000 : ℝ)^4359
        have hw : |(267007641/500000000 : ℝ)|=(267007641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-308950641/2000000000 : ℝ)|^5383 ≤ (2490284262293/25000000000000 : ℝ)^4359
        have hw : |(-308950641/2000000000 : ℝ)|=(308950641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139441853/10000000000 : ℝ)|^5383 ≤ (43954709400263/100000000000000 : ℝ)^4359
        have hw : |(5139441853/10000000000 : ℝ)|=(5139441853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s4_2 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340149439/10000000000 : ℝ)*x 0 + (40151909/78125000 : ℝ)*x 1 + (-1544754417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340149439/10000000000 : ℝ)^5383 ≤ (46084117497917/100000000000000 : ℝ)^4359 := by
    have hnat : (5340149439 : ℕ)^5383*100000000000000^4359 ≤ 46084117497917^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340149439 10000000000 46084117497917 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40151909/78125000 : ℝ)^5383 ≤ (343396373387/781250000000 : ℝ)^4359 := by
    have hnat : (40151909 : ℕ)^5383*781250000000^4359 ≤ 343396373387^4359*78125000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40151909 78125000 343396373387 781250000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1544754417/10000000000 : ℝ)^5383 ≤ (1992229340113/20000000000000 : ℝ)^4359 := by
    have hnat : (1544754417 : ℕ)^5383*20000000000000^4359 ≤ 1992229340113^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544754417 10000000000 1992229340113 20000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340149439/10000000000 : ℝ), (40151909/78125000 : ℝ), (-1544754417/10000000000 : ℝ)] ![(46084117497917/100000000000000 : ℝ), (343396373387/781250000000 : ℝ), (1992229340113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340149439/10000000000 : ℝ)|^5383 ≤ (46084117497917/100000000000000 : ℝ)^4359
        have hw : |(5340149439/10000000000 : ℝ)|=(5340149439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40151909/78125000 : ℝ)|^5383 ≤ (343396373387/781250000000 : ℝ)^4359
        have hw : |(40151909/78125000 : ℝ)|=(40151909/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1544754417/10000000000 : ℝ)|^5383 ≤ (1992229340113/20000000000000 : ℝ)^4359
        have hw : |(-1544754417/10000000000 : ℝ)|=(1544754417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s4_3 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511510181/1250000000 : ℝ)*x 0 + (1814346851/5000000000 : ℝ)*x 1 + (573784503/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511510181/1250000000 : ℝ)^5383 ≤ (33172917319919/100000000000000 : ℝ)^4359 := by
    have hnat : (511510181 : ℕ)^5383*100000000000000^4359 ≤ 33172917319919^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511510181 1250000000 33172917319919 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1814346851/5000000000 : ℝ)^5383 ≤ (14298764143669/50000000000000 : ℝ)^4359 := by
    have hnat : (1814346851 : ℕ)^5383*50000000000000^4359 ≤ 14298764143669^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814346851 5000000000 14298764143669 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573784503/1250000000 : ℝ)^5383 ≤ (19114777187361/50000000000000 : ℝ)^4359 := by
    have hnat : (573784503 : ℕ)^5383*50000000000000^4359 ≤ 19114777187361^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573784503 1250000000 19114777187361 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511510181/1250000000 : ℝ), (1814346851/5000000000 : ℝ), (573784503/1250000000 : ℝ)] ![(33172917319919/100000000000000 : ℝ), (14298764143669/50000000000000 : ℝ), (19114777187361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511510181/1250000000 : ℝ)|^5383 ≤ (33172917319919/100000000000000 : ℝ)^4359
        have hw : |(511510181/1250000000 : ℝ)|=(511510181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1814346851/5000000000 : ℝ)|^5383 ≤ (14298764143669/50000000000000 : ℝ)^4359
        have hw : |(1814346851/5000000000 : ℝ)|=(1814346851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(573784503/1250000000 : ℝ)|^5383 ≤ (19114777187361/50000000000000 : ℝ)^4359
        have hw : |(573784503/1250000000 : ℝ)|=(573784503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s4_4 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-172112403/1250000000 : ℝ)*x 0 + (5143063891/10000000000 : ℝ)*x 1 + (5460026063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172112403/1250000000 : ℝ)^5383 ≤ (4321019933999/50000000000000 : ℝ)^4359 := by
    have hnat : (172112403 : ℕ)^5383*50000000000000^4359 ≤ 4321019933999^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172112403 1250000000 4321019933999 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143063891/10000000000 : ℝ)^5383 ≤ (54991208551/125000000000 : ℝ)^4359 := by
    have hnat : (5143063891 : ℕ)^5383*125000000000^4359 ≤ 54991208551^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143063891 10000000000 54991208551 125000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460026063/10000000000 : ℝ)^5383 ≤ (23682496635179/50000000000000 : ℝ)^4359 := by
    have hnat : (5460026063 : ℕ)^5383*50000000000000^4359 ≤ 23682496635179^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460026063 10000000000 23682496635179 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-172112403/1250000000 : ℝ), (5143063891/10000000000 : ℝ), (5460026063/10000000000 : ℝ)] ![(4321019933999/50000000000000 : ℝ), (54991208551/125000000000 : ℝ), (23682496635179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-172112403/1250000000 : ℝ)|^5383 ≤ (4321019933999/50000000000000 : ℝ)^4359
        have hw : |(-172112403/1250000000 : ℝ)|=(172112403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143063891/10000000000 : ℝ)|^5383 ≤ (54991208551/125000000000 : ℝ)^4359
        have hw : |(5143063891/10000000000 : ℝ)|=(5143063891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460026063/10000000000 : ℝ)|^5383 ≤ (23682496635179/50000000000000 : ℝ)^4359
        have hw : |(5460026063/10000000000 : ℝ)|=(5460026063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s4_5 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253349821/10000000000 : ℝ)*x 0 + (273001281/500000000 : ℝ)*x 1 + (-1224171363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253349821/10000000000 : ℝ)^5383 ≤ (1411277078451/3125000000000 : ℝ)^4359 := by
    have hnat : (5253349821 : ℕ)^5383*3125000000000^4359 ≤ 1411277078451^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253349821 10000000000 1411277078451 3125000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273001281/500000000 : ℝ)^5383 ≤ (47364988524617/100000000000000 : ℝ)^4359 := by
    have hnat : (273001281 : ℕ)^5383*100000000000000^4359 ≤ 47364988524617^4359*500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273001281 500000000 47364988524617 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1224171363/10000000000 : ℝ)^5383 ≤ (467134059187/6250000000000 : ℝ)^4359 := by
    have hnat : (1224171363 : ℕ)^5383*6250000000000^4359 ≤ 467134059187^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224171363 10000000000 467134059187 6250000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253349821/10000000000 : ℝ), (273001281/500000000 : ℝ), (-1224171363/10000000000 : ℝ)] ![(1411277078451/3125000000000 : ℝ), (47364988524617/100000000000000 : ℝ), (467134059187/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253349821/10000000000 : ℝ)|^5383 ≤ (1411277078451/3125000000000 : ℝ)^4359
        have hw : |(5253349821/10000000000 : ℝ)|=(5253349821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273001281/500000000 : ℝ)|^5383 ≤ (47364988524617/100000000000000 : ℝ)^4359
        have hw : |(273001281/500000000 : ℝ)|=(273001281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1224171363/10000000000 : ℝ)|^5383 ≤ (467134059187/6250000000000 : ℝ)^4359
        have hw : |(-1224171363/10000000000 : ℝ)|=(1224171363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s4_6 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511563431/1250000000 : ℝ)*x 0 + (4579534859/10000000000 : ℝ)*x 1 + (3639599517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511563431/1250000000 : ℝ)^5383 ≤ (3317718205263/10000000000000 : ℝ)^4359 := by
    have hnat : (511563431 : ℕ)^5383*10000000000000^4359 ≤ 3317718205263^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511563431 1250000000 3317718205263 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4579534859/10000000000 : ℝ)^5383 ≤ (38119113489379/100000000000000 : ℝ)^4359 := by
    have hnat : (4579534859 : ℕ)^5383*100000000000000^4359 ≤ 38119113489379^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579534859 10000000000 38119113489379 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3639599517/10000000000 : ℝ)^5383 ≤ (28703704441771/100000000000000 : ℝ)^4359 := by
    have hnat : (3639599517 : ℕ)^5383*100000000000000^4359 ≤ 28703704441771^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3639599517 10000000000 28703704441771 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511563431/1250000000 : ℝ), (4579534859/10000000000 : ℝ), (3639599517/10000000000 : ℝ)] ![(3317718205263/10000000000000 : ℝ), (38119113489379/100000000000000 : ℝ), (28703704441771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511563431/1250000000 : ℝ)|^5383 ≤ (3317718205263/10000000000000 : ℝ)^4359
        have hw : |(511563431/1250000000 : ℝ)|=(511563431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4579534859/10000000000 : ℝ)|^5383 ≤ (38119113489379/100000000000000 : ℝ)^4359
        have hw : |(4579534859/10000000000 : ℝ)|=(4579534859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3639599517/10000000000 : ℝ)|^5383 ≤ (28703704441771/100000000000000 : ℝ)^4359
        have hw : |(3639599517/10000000000 : ℝ)|=(3639599517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1720_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5043/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5043/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5043/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5043/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5043/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5043/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5043/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5043/50000 : ℝ) ^ (5375/1024 : ℝ) ≤ (589518570986021/100000000000000000000 : ℝ) := by
    have hpowers : (5043/50000 : ℝ)^5375 ≤ (589518570986021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5043 : ℕ)^5375*100000000000000000000^1024 ≤ 589518570986021^1024*50000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5043 50000 589518570986021 100000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5043/50000 : ℝ)) (X := (589518570986021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17021/100000 : ℝ) ^ (5375/1024 : ℝ) ≤ (1838453345770071/20000000000000000000 : ℝ) := by
    have hpowers : (17021/100000 : ℝ)^5375 ≤ (1838453345770071/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17021 : ℕ)^5375*20000000000000000000^1024 ≤ 1838453345770071^1024*100000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17021 100000 1838453345770071 20000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17021/100000 : ℝ)) (X := (1838453345770071/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000589518570986021/50000000000000000000 : ℝ) ≤ (10000022461921339/10000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (50000589518570986021/50000000000000000000 : ℝ)^1024 ≤ (10000022461921339/10000000000000000 : ℝ)^5375 := by
      have hnat : (50000589518570986021 : ℕ)^1024*10000000000000000^5375 ≤ 10000022461921339^5375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000589518570986021 50000000000000000000 10000022461921339 10000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000022461921339/10000000000000000 : ℝ)) (X := (50000589518570986021/50000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501222723162479547/12500000000000000000 : ℝ) ≤ (2500046586751643/2500000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (12501222723162479547/12500000000000000000 : ℝ)^1024 ≤ (2500046586751643/2500000000000000 : ℝ)^5375 := by
      have hnat : (12501222723162479547 : ℕ)^1024*2500000000000000^5375 ≤ 2500046586751643^5375*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501222723162479547 12500000000000000000 2500046586751643 2500000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500046586751643/2500000000000000 : ℝ)) (X := (12501222723162479547/12500000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001838453345770071/10000000000000000000 : ℝ) ≤ (2000070046418361/2000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (10001838453345770071/10000000000000000000 : ℝ)^1024 ≤ (2000070046418361/2000000000000000 : ℝ)^5375 := by
      have hnat : (10001838453345770071 : ℕ)^1024*2000000000000000^5375 ≤ 2000070046418361^5375*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001838453345770071 10000000000000000000 2000070046418361 2000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000070046418361/2000000000000000 : ℝ)) (X := (10001838453345770071/10000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(589518570986021/100000000000000000000 : ℝ) ≤ ((69346849883485165889/69350000000000000000 : ℝ)+2*(163885085233/693500000000000 : ℝ)*(5043/50000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (69346849883485165889/69350000000000000000 : ℝ)+2*(163885085233/693500000000000 : ℝ)*(5043/50000 : ℝ)=(10000022461921339/10000000000000000 : ℝ) by norm_num, show 1+2*(589518570986021/100000000000000000000 : ℝ)=(50000589518570986021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1838453345770071/20000000000000000000 : ℝ)+(589518570986021/100000000000000000000 : ℝ) ≤ ((69346849883485165889/69350000000000000000 : ℝ)+(163885085233/693500000000000 : ℝ)*((17021/100000 : ℝ)+(5043/50000 : ℝ)))^(5375/1024 : ℝ) := by
    rw [show (69346849883485165889/69350000000000000000 : ℝ)+(163885085233/693500000000000 : ℝ)*((17021/100000 : ℝ)+(5043/50000 : ℝ))=(2500046586751643/2500000000000000 : ℝ) by norm_num, show 1+(1838453345770071/20000000000000000000 : ℝ)+(589518570986021/100000000000000000000 : ℝ)=(12501222723162479547/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1838453345770071/20000000000000000000 : ℝ) ≤ ((69346849883485165889/69350000000000000000 : ℝ)+2*(163885085233/693500000000000 : ℝ)*(17021/100000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (69346849883485165889/69350000000000000000 : ℝ)+2*(163885085233/693500000000000 : ℝ)*(17021/100000 : ℝ)=(2000070046418361/2000000000000000 : ℝ) by norm_num, show 1+2*(1838453345770071/20000000000000000000 : ℝ)=(10001838453345770071/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69346849883485165889/69350000000000000000 : ℝ)*(X 1 0+X 2 0)+(163885085233/693500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (5043/50000 : ℝ)) (hi := (17021/100000 : ℝ)) (c := (69346849883485165889/69350000000000000000 : ℝ)) (alpha := (163885085233/693500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69346849883485165889/69350000000000000000 : ℝ)*(X 0 1+X 2 1)+(163885085233/693500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (5043/50000 : ℝ)) (hi := (17021/100000 : ℝ)) (c := (69346849883485165889/69350000000000000000 : ℝ)) (alpha := (163885085233/693500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69346849883485165889/69350000000000000000 : ℝ)*(X 0 2+X 1 2)+(163885085233/693500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (5043/50000 : ℝ)) (hi := (17021/100000 : ℝ)) (c := (69346849883485165889/69350000000000000000 : ℝ)) (alpha := (163885085233/693500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-27535091/200000000 : ℝ)*X 0 0+(5463702429/10000000000 : ℝ)*X 0 1+(5139441071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267007641/500000000 : ℝ)*X 1 0+(-308950641/2000000000 : ℝ)*X 1 1+(5139441853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5340149439/10000000000 : ℝ)*X 2 0+(40151909/78125000 : ℝ)*X 2 1+(-1544754417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((511510181/1250000000 : ℝ)*X 0 0+(1814346851/5000000000 : ℝ)*X 0 1+(573784503/1250000000 : ℝ)*X 0 2+(511510181/1250000000 : ℝ)*X 1 0+(1814346851/5000000000 : ℝ)*X 1 1+(573784503/1250000000 : ℝ)*X 1 2+(511510181/1250000000 : ℝ)*X 2 0+(1814346851/5000000000 : ℝ)*X 2 1+(573784503/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-172112403/1250000000 : ℝ)*X 0 0+(5143063891/10000000000 : ℝ)*X 0 1+(5460026063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253349821/10000000000 : ℝ)*X 2 0+(273001281/500000000 : ℝ)*X 2 1+(-1224171363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s4_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((511563431/1250000000 : ℝ)*X 0 0+(4579534859/10000000000 : ℝ)*X 0 1+(3639599517/10000000000 : ℝ)*X 0 2+(511563431/1250000000 : ℝ)*X 1 0+(4579534859/10000000000 : ℝ)*X 1 1+(3639599517/10000000000 : ℝ)*X 1 2+(511563431/1250000000 : ℝ)*X 2 0+(4579534859/10000000000 : ℝ)*X 2 1+(3639599517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (485783780783959639659523671/433437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151207359/10000000000000 : ℝ)*(base19) + (324923309/100000000000000 : ℝ)*(base23) + (481451291/100000000000000 : ℝ)*(upper3) + (81890953/20000000000000 : ℝ)*(lower4) + (257747033795671/12500000000000 : ℝ)*(major0) + (257747033795671/12500000000000 : ℝ)*(major1) + (257747033795671/12500000000000 : ℝ)*(major2) + (1541984025765281/50000000000000 : ℝ)*(sp0) + (61679639392717/2000000000000 : ℝ)*(sp1) + (3083983074245277/100000000000000 : ℝ)*(sp2) + (1039961082745543/100000000000000 : ℝ)*(sp3) + (7715089439/50000000000000 : ℝ)*(sp4) + (41270427/50000000000000 : ℝ)*(sp5) + (62022787/781250000000 : ℝ)*(sp6) + (519984510831139/50000000000000 : ℝ)*(f.failure) + (3083983481709439/100000000000000 : ℝ)*(f.sum) + (34948589345561/8668750000000000000000000000 : ℝ)*base65 + (8495398918926883481/866875000000000000000000000000000 : ℝ)*base68 + (10149645172175633481/866875000000000000000000000000000 : ℝ)*base70 + (4911332999540633481/866875000000000000000000000000000 : ℝ)*base72 + (891413035141/2167187500000000000000000000 : ℝ)*base74 + (16454098357649383481/866875000000000000000000000000000 : ℝ)*base76 + (7646704821552508481/866875000000000000000000000000000 : ℝ)*base78 + (13000700506774383481/866875000000000000000000000000000 : ℝ)*base80 + (67213104641469/34675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9513631/1000000000000000000000 : ℝ)*base90 + (9513631/1000000000000000000000 : ℝ)*base92 + (9513631/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1720_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5043/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1720_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1720_box_0 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065683393/10000000000 : ℝ)*x 0 + (1352999209/2500000000 : ℝ)*x 1 + (5411997053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065683393/10000000000 : ℝ)^5383 ≤ (3148997024481/50000000000000 : ℝ)^4359 := by
    have hnat : (1065683393 : ℕ)^5383*50000000000000^4359 ≤ 3148997024481^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065683393 10000000000 3148997024481 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352999209/2500000000 : ℝ)^5383 ≤ (23425500903887/50000000000000 : ℝ)^4359 := by
    have hnat : (1352999209 : ℕ)^5383*50000000000000^4359 ≤ 23425500903887^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352999209 2500000000 23425500903887 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411997053/10000000000 : ℝ)^5383 ≤ (46851004127617/100000000000000 : ℝ)^4359 := by
    have hnat : (5411997053 : ℕ)^5383*100000000000000^4359 ≤ 46851004127617^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411997053 10000000000 46851004127617 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065683393/10000000000 : ℝ), (1352999209/2500000000 : ℝ), (5411997053/10000000000 : ℝ)] ![(3148997024481/50000000000000 : ℝ), (23425500903887/50000000000000 : ℝ), (46851004127617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065683393/10000000000 : ℝ)|^5383 ≤ (3148997024481/50000000000000 : ℝ)^4359
        have hw : |(-1065683393/10000000000 : ℝ)|=(1065683393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352999209/2500000000 : ℝ)|^5383 ≤ (23425500903887/50000000000000 : ℝ)^4359
        have hw : |(1352999209/2500000000 : ℝ)|=(1352999209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411997053/10000000000 : ℝ)|^5383 ≤ (46851004127617/100000000000000 : ℝ)^4359
        have hw : |(5411997053/10000000000 : ℝ)|=(5411997053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_1 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224853057/10000000000 : ℝ)*x 0 + (-665680833/5000000000 : ℝ)*x 1 + (2705998231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224853057/10000000000 : ℝ)^5383 ≤ (44858536110887/100000000000000 : ℝ)^4359 := by
    have hnat : (5224853057 : ℕ)^5383*100000000000000^4359 ≤ 44858536110887^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224853057 10000000000 44858536110887 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (665680833/5000000000 : ℝ)^5383 ≤ (64769266187/781250000000 : ℝ)^4359 := by
    have hnat : (665680833 : ℕ)^5383*781250000000^4359 ≤ 64769266187^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665680833 5000000000 64769266187 781250000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705998231/5000000000 : ℝ)^5383 ≤ (46850997809519/100000000000000 : ℝ)^4359 := by
    have hnat : (2705998231 : ℕ)^5383*100000000000000^4359 ≤ 46850997809519^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705998231 5000000000 46850997809519 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224853057/10000000000 : ℝ), (-665680833/5000000000 : ℝ), (2705998231/5000000000 : ℝ)] ![(44858536110887/100000000000000 : ℝ), (64769266187/781250000000 : ℝ), (46850997809519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224853057/10000000000 : ℝ)|^5383 ≤ (44858536110887/100000000000000 : ℝ)^4359
        have hw : |(5224853057/10000000000 : ℝ)|=(5224853057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-665680833/5000000000 : ℝ)|^5383 ≤ (64769266187/781250000000 : ℝ)^4359
        have hw : |(-665680833/5000000000 : ℝ)|=(665680833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705998231/5000000000 : ℝ)|^5383 ≤ (46850997809519/100000000000000 : ℝ)^4359
        have hw : |(2705998231/5000000000 : ℝ)|=(2705998231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_2 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224852417/10000000000 : ℝ)*x 0 + (1352999281/2500000000 : ℝ)*x 1 + (-332840407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224852417/10000000000 : ℝ)^5383 ≤ (44858529325283/100000000000000 : ℝ)^4359 := by
    have hnat : (5224852417 : ℕ)^5383*100000000000000^4359 ≤ 44858529325283^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224852417 10000000000 44858529325283 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352999281/2500000000 : ℝ)^5383 ≤ (11712751221661/25000000000000 : ℝ)^4359 := by
    have hnat : (1352999281 : ℕ)^5383*25000000000000^4359 ≤ 11712751221661^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352999281 2500000000 11712751221661 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332840407/2500000000 : ℝ)^5383 ≤ (207261644493/2500000000000 : ℝ)^4359 := by
    have hnat : (332840407 : ℕ)^5383*2500000000000^4359 ≤ 207261644493^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332840407 2500000000 207261644493 2500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224852417/10000000000 : ℝ), (1352999281/2500000000 : ℝ), (-332840407/2500000000 : ℝ)] ![(44858529325283/100000000000000 : ℝ), (11712751221661/25000000000000 : ℝ), (207261644493/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224852417/10000000000 : ℝ)|^5383 ≤ (44858529325283/100000000000000 : ℝ)^4359
        have hw : |(5224852417/10000000000 : ℝ)|=(5224852417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352999281/2500000000 : ℝ)|^5383 ≤ (11712751221661/25000000000000 : ℝ)^4359
        have hw : |(1352999281/2500000000 : ℝ)|=(1352999281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-332840407/2500000000 : ℝ)|^5383 ≤ (207261644493/2500000000000 : ℝ)^4359
        have hw : |(-332840407/2500000000 : ℝ)|=(332840407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_3 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4472928409/10000000000 : ℝ)*x 0 + (1961414369/5000000000 : ℝ)*x 1 + (3922828623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4472928409/10000000000 : ℝ)^5383 ≤ (37026299723253/100000000000000 : ℝ)^4359 := by
    have hnat : (4472928409 : ℕ)^5383*100000000000000^4359 ≤ 37026299723253^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472928409 10000000000 37026299723253 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1961414369/5000000000 : ℝ)^5383 ≤ (31486850702767/100000000000000 : ℝ)^4359 := by
    have hnat : (1961414369 : ℕ)^5383*100000000000000^4359 ≤ 31486850702767^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961414369 5000000000 31486850702767 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3922828623/10000000000 : ℝ)^5383 ≤ (31486849562871/100000000000000 : ℝ)^4359 := by
    have hnat : (3922828623 : ℕ)^5383*100000000000000^4359 ≤ 31486849562871^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3922828623 10000000000 31486849562871 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4472928409/10000000000 : ℝ), (1961414369/5000000000 : ℝ), (3922828623/10000000000 : ℝ)] ![(37026299723253/100000000000000 : ℝ), (31486850702767/100000000000000 : ℝ), (31486849562871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4472928409/10000000000 : ℝ)|^5383 ≤ (37026299723253/100000000000000 : ℝ)^4359
        have hw : |(4472928409/10000000000 : ℝ)|=(4472928409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1961414369/5000000000 : ℝ)|^5383 ≤ (31486850702767/100000000000000 : ℝ)^4359
        have hw : |(1961414369/5000000000 : ℝ)|=(1961414369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3922828623/10000000000 : ℝ)|^5383 ≤ (31486849562871/100000000000000 : ℝ)^4359
        have hw : |(3922828623/10000000000 : ℝ)|=(3922828623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_4 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-854147453/5000000000 : ℝ)*x 0 + (5177819061/10000000000 : ℝ)*x 1 + (5177818987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854147453/5000000000 : ℝ)^5383 ≤ (88118968789/781250000000 : ℝ)^4359 := by
    have hnat : (854147453 : ℕ)^5383*781250000000^4359 ≤ 88118968789^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854147453 5000000000 88118968789 781250000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177819061/10000000000 : ℝ)^5383 ≤ (5545048297689/12500000000000 : ℝ)^4359 := by
    have hnat : (5177819061 : ℕ)^5383*12500000000000^4359 ≤ 5545048297689^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177819061 10000000000 5545048297689 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177818987/10000000000 : ℝ)^5383 ≤ (44360385598591/100000000000000 : ℝ)^4359 := by
    have hnat : (5177818987 : ℕ)^5383*100000000000000^4359 ≤ 44360385598591^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177818987 10000000000 44360385598591 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-854147453/5000000000 : ℝ), (5177819061/10000000000 : ℝ), (5177818987/10000000000 : ℝ)] ![(88118968789/781250000000 : ℝ), (5545048297689/12500000000000 : ℝ), (44360385598591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-854147453/5000000000 : ℝ)|^5383 ≤ (88118968789/781250000000 : ℝ)^4359
        have hw : |(-854147453/5000000000 : ℝ)|=(854147453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177819061/10000000000 : ℝ)|^5383 ≤ (5545048297689/12500000000000 : ℝ)^4359
        have hw : |(5177819061/10000000000 : ℝ)|=(5177819061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177818987/10000000000 : ℝ)|^5383 ≤ (44360385598591/100000000000000 : ℝ)^4359
        have hw : |(5177818987/10000000000 : ℝ)|=(5177818987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_5 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168227857/312500000 : ℝ)*x 0 + (-35877283/250000000 : ℝ)*x 1 + (1035563819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168227857/312500000 : ℝ)^5383 ≤ (46544317450159/100000000000000 : ℝ)^4359 := by
    have hnat : (168227857 : ℕ)^5383*100000000000000^4359 ≤ 46544317450159^4359*312500000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168227857 312500000 46544317450159 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35877283/250000000 : ℝ)^5383 ≤ (2273823948169/25000000000000 : ℝ)^4359 := by
    have hnat : (35877283 : ℕ)^5383*25000000000000^4359 ≤ 2273823948169^4359*250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35877283 250000000 2273823948169 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035563819/2000000000 : ℝ)^5383 ≤ (2772524171327/6250000000000 : ℝ)^4359 := by
    have hnat : (1035563819 : ℕ)^5383*6250000000000^4359 ≤ 2772524171327^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035563819 2000000000 2772524171327 6250000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168227857/312500000 : ℝ), (-35877283/250000000 : ℝ), (1035563819/2000000000 : ℝ)] ![(46544317450159/100000000000000 : ℝ), (2273823948169/25000000000000 : ℝ), (2772524171327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168227857/312500000 : ℝ)|^5383 ≤ (46544317450159/100000000000000 : ℝ)^4359
        have hw : |(168227857/312500000 : ℝ)|=(168227857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35877283/250000000 : ℝ)|^5383 ≤ (2273823948169/25000000000000 : ℝ)^4359
        have hw : |(-35877283/250000000 : ℝ)|=(35877283/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035563819/2000000000 : ℝ)|^5383 ≤ (2772524171327/6250000000000 : ℝ)^4359
        have hw : |(1035563819/2000000000 : ℝ)|=(1035563819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_6 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691645683/5000000000 : ℝ)*x 0 + (647227387/1250000000 : ℝ)*x 1 + (-1435091397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691645683/5000000000 : ℝ)^5383 ≤ (46544316830883/100000000000000 : ℝ)^4359 := by
    have hnat : (2691645683 : ℕ)^5383*100000000000000^4359 ≤ 46544316830883^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691645683 5000000000 46544316830883 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647227387/1250000000 : ℝ)^5383 ≤ (11090096687953/25000000000000 : ℝ)^4359 := by
    have hnat : (647227387 : ℕ)^5383*25000000000000^4359 ≤ 11090096687953^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647227387 1250000000 11090096687953 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435091397/10000000000 : ℝ)^5383 ≤ (4547648197663/50000000000000 : ℝ)^4359 := by
    have hnat : (1435091397 : ℕ)^5383*50000000000000^4359 ≤ 4547648197663^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435091397 10000000000 4547648197663 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691645683/5000000000 : ℝ), (647227387/1250000000 : ℝ), (-1435091397/10000000000 : ℝ)] ![(46544316830883/100000000000000 : ℝ), (11090096687953/25000000000000 : ℝ), (4547648197663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691645683/5000000000 : ℝ)|^5383 ≤ (46544316830883/100000000000000 : ℝ)^4359
        have hw : |(2691645683/5000000000 : ℝ)|=(2691645683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647227387/1250000000 : ℝ)|^5383 ≤ (11090096687953/25000000000000 : ℝ)^4359
        have hw : |(647227387/1250000000 : ℝ)|=(647227387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1435091397/10000000000 : ℝ)|^5383 ≤ (4547648197663/50000000000000 : ℝ)^4359
        have hw : |(-1435091397/10000000000 : ℝ)|=(1435091397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_7 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3695061773/10000000000 : ℝ)*x 0 + (2155474977/5000000000 : ℝ)*x 1 + (4310949803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3695061773/10000000000 : ℝ)^5383 ≤ (14622411882629/50000000000000 : ℝ)^4359 := by
    have hnat : (3695061773 : ℕ)^5383*50000000000000^4359 ≤ 14622411882629^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695061773 10000000000 14622411882629 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155474977/5000000000 : ℝ)^5383 ≤ (35377588875063/100000000000000 : ℝ)^4359 := by
    have hnat : (2155474977 : ℕ)^5383*100000000000000^4359 ≤ 35377588875063^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155474977 5000000000 35377588875063 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4310949803/10000000000 : ℝ)^5383 ≤ (35377587344787/100000000000000 : ℝ)^4359 := by
    have hnat : (4310949803 : ℕ)^5383*100000000000000^4359 ≤ 35377587344787^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310949803 10000000000 35377587344787 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3695061773/10000000000 : ℝ), (2155474977/5000000000 : ℝ), (4310949803/10000000000 : ℝ)] ![(14622411882629/50000000000000 : ℝ), (35377588875063/100000000000000 : ℝ), (35377587344787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3695061773/10000000000 : ℝ)|^5383 ≤ (14622411882629/50000000000000 : ℝ)^4359
        have hw : |(3695061773/10000000000 : ℝ)|=(3695061773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2155474977/5000000000 : ℝ)|^5383 ≤ (35377588875063/100000000000000 : ℝ)^4359
        have hw : |(2155474977/5000000000 : ℝ)|=(2155474977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4310949803/10000000000 : ℝ)|^5383 ≤ (35377587344787/100000000000000 : ℝ)^4359
        have hw : |(4310949803/10000000000 : ℝ)|=(4310949803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_8 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-784975591/5000000000 : ℝ)*x 0 + (156390363/312500000 : ℝ)*x 1 + (68179113/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784975591/5000000000 : ℝ)^5383 ≤ (5081088152271/50000000000000 : ℝ)^4359 := by
    have hnat : (784975591 : ℕ)^5383*50000000000000^4359 ≤ 5081088152271^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784975591 5000000000 5081088152271 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156390363/312500000 : ℝ)^5383 ≤ (425338536147/1000000000000 : ℝ)^4359 := by
    have hnat : (156390363 : ℕ)^5383*1000000000000^4359 ≤ 425338536147^4359*312500000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156390363 312500000 425338536147 1000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68179113/125000000 : ℝ)^5383 ≤ (1478249064581/3125000000000 : ℝ)^4359 := by
    have hnat : (68179113 : ℕ)^5383*3125000000000^4359 ≤ 1478249064581^4359*125000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68179113 125000000 1478249064581 3125000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-784975591/5000000000 : ℝ), (156390363/312500000 : ℝ), (68179113/125000000 : ℝ)] ![(5081088152271/50000000000000 : ℝ), (425338536147/1000000000000 : ℝ), (1478249064581/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-784975591/5000000000 : ℝ)|^5383 ≤ (5081088152271/50000000000000 : ℝ)^4359
        have hw : |(-784975591/5000000000 : ℝ)|=(784975591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156390363/312500000 : ℝ)|^5383 ≤ (425338536147/1000000000000 : ℝ)^4359
        have hw : |(156390363/312500000 : ℝ)|=(156390363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68179113/125000000 : ℝ)|^5383 ≤ (1478249064581/3125000000000 : ℝ)^4359
        have hw : |(68179113/125000000 : ℝ)|=(68179113/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_9 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519623347/1000000000 : ℝ)*x 0 + (-65592819/500000000 : ℝ)*x 1 + (5454329609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519623347/1000000000 : ℝ)^5383 ≤ (5569411533801/12500000000000 : ℝ)^4359 := by
    have hnat : (519623347 : ℕ)^5383*12500000000000^4359 ≤ 5569411533801^4359*1000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519623347 1000000000 5569411533801 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65592819/500000000 : ℝ)^5383 ≤ (162814631119/2000000000000 : ℝ)^4359 := by
    have hnat : (65592819 : ℕ)^5383*2000000000000^4359 ≤ 162814631119^4359*500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65592819 500000000 162814631119 2000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454329609/10000000000 : ℝ)^5383 ≤ (23651988080321/50000000000000 : ℝ)^4359 := by
    have hnat : (5454329609 : ℕ)^5383*50000000000000^4359 ≤ 23651988080321^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454329609 10000000000 23651988080321 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519623347/1000000000 : ℝ), (-65592819/500000000 : ℝ), (5454329609/10000000000 : ℝ)] ![(5569411533801/12500000000000 : ℝ), (162814631119/2000000000000 : ℝ), (23651988080321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519623347/1000000000 : ℝ)|^5383 ≤ (5569411533801/12500000000000 : ℝ)^4359
        have hw : |(519623347/1000000000 : ℝ)|=(519623347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65592819/500000000 : ℝ)|^5383 ≤ (162814631119/2000000000000 : ℝ)^4359
        have hw : |(-65592819/500000000 : ℝ)|=(65592819/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454329609/10000000000 : ℝ)|^5383 ≤ (23651988080321/50000000000000 : ℝ)^4359
        have hw : |(5454329609/10000000000 : ℝ)|=(5454329609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_10 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299058623/2500000000 : ℝ)*x 0 + (5454329031/10000000000 : ℝ)*x 1 + (-40995493/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299058623/2500000000 : ℝ)^5383 ≤ (44555303092197/100000000000000 : ℝ)^4359 := by
    have hnat : (1299058623 : ℕ)^5383*100000000000000^4359 ≤ 44555303092197^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299058623 2500000000 44555303092197 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454329031/10000000000 : ℝ)^5383 ≤ (47303969970201/100000000000000 : ℝ)^4359 := by
    have hnat : (5454329031 : ℕ)^5383*100000000000000^4359 ≤ 47303969970201^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454329031 10000000000 47303969970201 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40995493/312500000 : ℝ)^5383 ≤ (814072692733/10000000000000 : ℝ)^4359 := by
    have hnat : (40995493 : ℕ)^5383*10000000000000^4359 ≤ 814072692733^4359*312500000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40995493 312500000 814072692733 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299058623/2500000000 : ℝ), (5454329031/10000000000 : ℝ), (-40995493/312500000 : ℝ)] ![(44555303092197/100000000000000 : ℝ), (47303969970201/100000000000000 : ℝ), (814072692733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299058623/2500000000 : ℝ)|^5383 ≤ (44555303092197/100000000000000 : ℝ)^4359
        have hw : |(1299058623/2500000000 : ℝ)|=(1299058623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454329031/10000000000 : ℝ)|^5383 ≤ (47303969970201/100000000000000 : ℝ)^4359
        have hw : |(5454329031/10000000000 : ℝ)|=(5454329031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40995493/312500000 : ℝ)|^5383 ≤ (814072692733/10000000000000 : ℝ)^4359
        have hw : |(-40995493/312500000 : ℝ)|=(40995493/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_11 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2304289743/5000000000 : ℝ)*x 0 + (120390149/312500000 : ℝ)*x 1 + (3852482281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2304289743/5000000000 : ℝ)^5383 ≤ (38417890806507/100000000000000 : ℝ)^4359 := by
    have hnat : (2304289743 : ℕ)^5383*100000000000000^4359 ≤ 38417890806507^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304289743 5000000000 38417890806507 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120390149/312500000 : ℝ)^5383 ≤ (30791066862479/100000000000000 : ℝ)^4359 := by
    have hnat : (120390149 : ℕ)^5383*100000000000000^4359 ≤ 30791066862479^4359*312500000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120390149 312500000 30791066862479 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3852482281/10000000000 : ℝ)^5383 ≤ (7697760578889/25000000000000 : ℝ)^4359 := by
    have hnat : (3852482281 : ℕ)^5383*25000000000000^4359 ≤ 7697760578889^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3852482281 10000000000 7697760578889 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2304289743/5000000000 : ℝ), (120390149/312500000 : ℝ), (3852482281/10000000000 : ℝ)] ![(38417890806507/100000000000000 : ℝ), (30791066862479/100000000000000 : ℝ), (7697760578889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2304289743/5000000000 : ℝ)|^5383 ≤ (38417890806507/100000000000000 : ℝ)^4359
        have hw : |(2304289743/5000000000 : ℝ)|=(2304289743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(120390149/312500000 : ℝ)|^5383 ≤ (30791066862479/100000000000000 : ℝ)^4359
        have hw : |(120390149/312500000 : ℝ)|=(120390149/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3852482281/10000000000 : ℝ)|^5383 ≤ (7697760578889/25000000000000 : ℝ)^4359
        have hw : |(3852482281/10000000000 : ℝ)|=(3852482281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_12 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-599149473/5000000000 : ℝ)*x 0 + (5577303937/10000000000 : ℝ)*x 1 + (5152808741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (599149473/5000000000 : ℝ)^5383 ≤ (7279560338599/100000000000000 : ℝ)^4359 := by
    have hnat : (599149473 : ℕ)^5383*100000000000000^4359 ≤ 7279560338599^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599149473 5000000000 7279560338599 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5577303937/10000000000 : ℝ)^5383 ≤ (48624512323097/100000000000000 : ℝ)^4359 := by
    have hnat : (5577303937 : ℕ)^5383*100000000000000^4359 ≤ 48624512323097^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5577303937 10000000000 48624512323097 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152808741/10000000000 : ℝ)^5383 ≤ (44095927330133/100000000000000 : ℝ)^4359 := by
    have hnat : (5152808741 : ℕ)^5383*100000000000000^4359 ≤ 44095927330133^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152808741 10000000000 44095927330133 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-599149473/5000000000 : ℝ), (5577303937/10000000000 : ℝ), (5152808741/10000000000 : ℝ)] ![(7279560338599/100000000000000 : ℝ), (48624512323097/100000000000000 : ℝ), (44095927330133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-599149473/5000000000 : ℝ)|^5383 ≤ (7279560338599/100000000000000 : ℝ)^4359
        have hw : |(-599149473/5000000000 : ℝ)|=(599149473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5577303937/10000000000 : ℝ)|^5383 ≤ (48624512323097/100000000000000 : ℝ)^4359
        have hw : |(5577303937/10000000000 : ℝ)|=(5577303937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152808741/10000000000 : ℝ)|^5383 ≤ (44095927330133/100000000000000 : ℝ)^4359
        have hw : |(5152808741/10000000000 : ℝ)|=(5152808741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_13 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400244917/10000000000 : ℝ)*x 0 + (-1445734963/10000000000 : ℝ)*x 1 + (5152808821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400244917/10000000000 : ℝ)^5383 ≤ (46725399735919/100000000000000 : ℝ)^4359 := by
    have hnat : (5400244917 : ℕ)^5383*100000000000000^4359 ≤ 46725399735919^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400244917 10000000000 46725399735919 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1445734963/10000000000 : ℝ)^5383 ≤ (9178672081283/100000000000000 : ℝ)^4359 := by
    have hnat : (1445734963 : ℕ)^5383*100000000000000^4359 ≤ 9178672081283^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445734963 10000000000 9178672081283 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152808821/10000000000 : ℝ)^5383 ≤ (11023982043893/25000000000000 : ℝ)^4359 := by
    have hnat : (5152808821 : ℕ)^5383*25000000000000^4359 ≤ 11023982043893^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152808821 10000000000 11023982043893 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400244917/10000000000 : ℝ), (-1445734963/10000000000 : ℝ), (5152808821/10000000000 : ℝ)] ![(46725399735919/100000000000000 : ℝ), (9178672081283/100000000000000 : ℝ), (11023982043893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400244917/10000000000 : ℝ)|^5383 ≤ (46725399735919/100000000000000 : ℝ)^4359
        have hw : |(5400244917/10000000000 : ℝ)|=(5400244917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1445734963/10000000000 : ℝ)|^5383 ≤ (9178672081283/100000000000000 : ℝ)^4359
        have hw : |(-1445734963/10000000000 : ℝ)|=(1445734963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152808821/10000000000 : ℝ)|^5383 ≤ (11023982043893/25000000000000 : ℝ)^4359
        have hw : |(5152808821/10000000000 : ℝ)|=(5152808821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_14 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400245001/10000000000 : ℝ)*x 0 + (206112351/400000000 : ℝ)*x 1 + (-1445734909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400245001/10000000000 : ℝ)^5383 ≤ (9345080126693/20000000000000 : ℝ)^4359 := by
    have hnat : (5400245001 : ℕ)^5383*20000000000000^4359 ≤ 9345080126693^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400245001 10000000000 9345080126693 20000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206112351/400000000 : ℝ)^5383 ≤ (8819185537889/20000000000000 : ℝ)^4359 := by
    have hnat : (206112351 : ℕ)^5383*20000000000000^4359 ≤ 8819185537889^4359*400000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206112351 400000000 8819185537889 20000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1445734909/10000000000 : ℝ)^5383 ≤ (9178671657911/100000000000000 : ℝ)^4359 := by
    have hnat : (1445734909 : ℕ)^5383*100000000000000^4359 ≤ 9178671657911^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445734909 10000000000 9178671657911 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400245001/10000000000 : ℝ), (206112351/400000000 : ℝ), (-1445734909/10000000000 : ℝ)] ![(9345080126693/20000000000000 : ℝ), (8819185537889/20000000000000 : ℝ), (9178671657911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400245001/10000000000 : ℝ)|^5383 ≤ (9345080126693/20000000000000 : ℝ)^4359
        have hw : |(5400245001/10000000000 : ℝ)|=(5400245001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206112351/400000000 : ℝ)|^5383 ≤ (8819185537889/20000000000000 : ℝ)^4359
        have hw : |(206112351/400000000 : ℝ)|=(206112351/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1445734909/10000000000 : ℝ)|^5383 ≤ (9178671657911/100000000000000 : ℝ)^4359
        have hw : |(-1445734909/10000000000 : ℝ)|=(1445734909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_box_15 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (360900261/1000000000 : ℝ)*x 0 + (870457669/2000000000 : ℝ)*x 1 + (4352288397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360900261/1000000000 : ℝ)^5383 ≤ (7101502724437/25000000000000 : ℝ)^4359 := by
    have hnat : (360900261 : ℕ)^5383*25000000000000^4359 ≤ 7101502724437^4359*1000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360900261 1000000000 7101502724437 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (870457669/2000000000 : ℝ)^5383 ≤ (7159398855541/20000000000000 : ℝ)^4359 := by
    have hnat : (870457669 : ℕ)^5383*20000000000000^4359 ≤ 7159398855541^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870457669 2000000000 7159398855541 20000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4352288397/10000000000 : ℝ)^5383 ≤ (3579699480587/10000000000000 : ℝ)^4359 := by
    have hnat : (4352288397 : ℕ)^5383*10000000000000^4359 ≤ 3579699480587^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352288397 10000000000 3579699480587 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(360900261/1000000000 : ℝ), (870457669/2000000000 : ℝ), (4352288397/10000000000 : ℝ)] ![(7101502724437/25000000000000 : ℝ), (7159398855541/20000000000000 : ℝ), (3579699480587/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(360900261/1000000000 : ℝ)|^5383 ≤ (7101502724437/25000000000000 : ℝ)^4359
        have hw : |(360900261/1000000000 : ℝ)|=(360900261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(870457669/2000000000 : ℝ)|^5383 ≤ (7159398855541/20000000000000 : ℝ)^4359
        have hw : |(870457669/2000000000 : ℝ)|=(870457669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4352288397/10000000000 : ℝ)|^5383 ≤ (3579699480587/10000000000000 : ℝ)^4359
        have hw : |(4352288397/10000000000 : ℝ)|=(4352288397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1720_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66843/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14659/25000 : ℝ) ∧ (409/500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (22641/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10087/100000 : ℝ) ^ (5375/1024 : ℝ) ≤ (589825436806829/100000000000000000000 : ℝ) := by
    have hpowers : (10087/100000 : ℝ)^5375 ≤ (589825436806829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10087 : ℕ)^5375*100000000000000000000^1024 ≤ 589825436806829^1024*100000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10087 100000 589825436806829 100000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10087/100000 : ℝ)) (X := (589825436806829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17021/100000 : ℝ) ^ (5375/1024 : ℝ) ≤ (1838453345770071/20000000000000000000 : ℝ) := by
    have hpowers : (17021/100000 : ℝ)^5375 ≤ (1838453345770071/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17021 : ℕ)^5375*20000000000000000000^1024 ≤ 1838453345770071^1024*100000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17021 100000 1838453345770071 20000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17021/100000 : ℝ)) (X := (1838453345770071/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000589825436806829/50000000000000000000 : ℝ) ≤ (1250002809201691/1250000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (50000589825436806829/50000000000000000000 : ℝ)^1024 ≤ (1250002809201691/1250000000000000 : ℝ)^5375 := by
      have hnat : (50000589825436806829 : ℕ)^1024*1250000000000000^5375 ≤ 1250002809201691^5375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000589825436806829 50000000000000000000 1250002809201691 1250000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002809201691/1250000000000000 : ℝ)) (X := (50000589825436806829/50000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125305690380176787/3125000000000000000 : ℝ) ≤ (10000186352852259/10000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (3125305690380176787/3125000000000000000 : ℝ)^1024 ≤ (10000186352852259/10000000000000000 : ℝ)^5375 := by
      have hnat : (3125305690380176787 : ℕ)^1024*10000000000000000^5375 ≤ 10000186352852259^5375*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125305690380176787 3125000000000000000 10000186352852259 10000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000186352852259/10000000000000000 : ℝ)) (X := (3125305690380176787/3125000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001838453345770071/10000000000000000000 : ℝ) ≤ (1000035023209099/1000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (10001838453345770071/10000000000000000000 : ℝ)^1024 ≤ (1000035023209099/1000000000000000 : ℝ)^5375 := by
      have hnat : (10001838453345770071 : ℕ)^1024*1000000000000000^5375 ≤ 1000035023209099^5375*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001838453345770071 10000000000000000000 1000035023209099 1000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000035023209099/1000000000000000 : ℝ)) (X := (10001838453345770071/10000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(589825436806829/100000000000000000000 : ℝ) ≤ ((34668424866137021979/34670000000000000000 : ℝ)+2*(163879238731/693400000000000 : ℝ)*(10087/100000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (34668424866137021979/34670000000000000000 : ℝ)+2*(163879238731/693400000000000 : ℝ)*(10087/100000 : ℝ)=(1250002809201691/1250000000000000 : ℝ) by norm_num, show 1+2*(589825436806829/100000000000000000000 : ℝ)=(50000589825436806829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1838453345770071/20000000000000000000 : ℝ)+(589825436806829/100000000000000000000 : ℝ) ≤ ((34668424866137021979/34670000000000000000 : ℝ)+(163879238731/693400000000000 : ℝ)*((17021/100000 : ℝ)+(10087/100000 : ℝ)))^(5375/1024 : ℝ) := by
    rw [show (34668424866137021979/34670000000000000000 : ℝ)+(163879238731/693400000000000 : ℝ)*((17021/100000 : ℝ)+(10087/100000 : ℝ))=(10000186352852259/10000000000000000 : ℝ) by norm_num, show 1+(1838453345770071/20000000000000000000 : ℝ)+(589825436806829/100000000000000000000 : ℝ)=(3125305690380176787/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1838453345770071/20000000000000000000 : ℝ) ≤ ((34668424866137021979/34670000000000000000 : ℝ)+2*(163879238731/693400000000000 : ℝ)*(17021/100000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (34668424866137021979/34670000000000000000 : ℝ)+2*(163879238731/693400000000000 : ℝ)*(17021/100000 : ℝ)=(1000035023209099/1000000000000000 : ℝ) by norm_num, show 1+2*(1838453345770071/20000000000000000000 : ℝ)=(10001838453345770071/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34668424866137021979/34670000000000000000 : ℝ)*(X 1 0+X 2 0)+(163879238731/693400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (10087/100000 : ℝ)) (hi := (17021/100000 : ℝ)) (c := (34668424866137021979/34670000000000000000 : ℝ)) (alpha := (163879238731/693400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34668424866137021979/34670000000000000000 : ℝ)*(X 0 1+X 2 1)+(163879238731/693400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (10087/100000 : ℝ)) (hi := (17021/100000 : ℝ)) (c := (34668424866137021979/34670000000000000000 : ℝ)) (alpha := (163879238731/693400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34668424866137021979/34670000000000000000 : ℝ)*(X 0 2+X 1 2)+(163879238731/693400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (10087/100000 : ℝ)) (hi := (17021/100000 : ℝ)) (c := (34668424866137021979/34670000000000000000 : ℝ)) (alpha := (163879238731/693400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1065683393/10000000000 : ℝ)*X 0 0+(1352999209/2500000000 : ℝ)*X 0 1+(5411997053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5224853057/10000000000 : ℝ)*X 1 0+(-665680833/5000000000 : ℝ)*X 1 1+(2705998231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224852417/10000000000 : ℝ)*X 2 0+(1352999281/2500000000 : ℝ)*X 2 1+(-332840407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4472928409/10000000000 : ℝ)*X 0 0+(1961414369/5000000000 : ℝ)*X 0 1+(3922828623/10000000000 : ℝ)*X 0 2+(4472928409/10000000000 : ℝ)*X 1 0+(1961414369/5000000000 : ℝ)*X 1 1+(3922828623/10000000000 : ℝ)*X 1 2+(4472928409/10000000000 : ℝ)*X 2 0+(1961414369/5000000000 : ℝ)*X 2 1+(3922828623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-854147453/5000000000 : ℝ)*X 0 0+(5177819061/10000000000 : ℝ)*X 0 1+(5177818987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((168227857/312500000 : ℝ)*X 1 0+(-35877283/250000000 : ℝ)*X 1 1+(1035563819/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691645683/5000000000 : ℝ)*X 2 0+(647227387/1250000000 : ℝ)*X 2 1+(-1435091397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3695061773/10000000000 : ℝ)*X 0 0+(2155474977/5000000000 : ℝ)*X 0 1+(4310949803/10000000000 : ℝ)*X 0 2+(3695061773/10000000000 : ℝ)*X 1 0+(2155474977/5000000000 : ℝ)*X 1 1+(4310949803/10000000000 : ℝ)*X 1 2+(3695061773/10000000000 : ℝ)*X 2 0+(2155474977/5000000000 : ℝ)*X 2 1+(4310949803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-784975591/5000000000 : ℝ)*X 0 0+(156390363/312500000 : ℝ)*X 0 1+(68179113/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((519623347/1000000000 : ℝ)*X 1 0+(-65592819/500000000 : ℝ)*X 1 1+(5454329609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1299058623/2500000000 : ℝ)*X 2 0+(5454329031/10000000000 : ℝ)*X 2 1+(-40995493/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2304289743/5000000000 : ℝ)*X 0 0+(120390149/312500000 : ℝ)*X 0 1+(3852482281/10000000000 : ℝ)*X 0 2+(2304289743/5000000000 : ℝ)*X 1 0+(120390149/312500000 : ℝ)*X 1 1+(3852482281/10000000000 : ℝ)*X 1 2+(2304289743/5000000000 : ℝ)*X 2 0+(120390149/312500000 : ℝ)*X 2 1+(3852482281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-599149473/5000000000 : ℝ)*X 0 0+(5577303937/10000000000 : ℝ)*X 0 1+(5152808741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5400244917/10000000000 : ℝ)*X 1 0+(-1445734963/10000000000 : ℝ)*X 1 1+(5152808821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5400245001/10000000000 : ℝ)*X 2 0+(206112351/400000000 : ℝ)*X 2 1+(-1445734909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((360900261/1000000000 : ℝ)*X 0 0+(870457669/2000000000 : ℝ)*X 0 1+(4352288397/10000000000 : ℝ)*X 0 2+(360900261/1000000000 : ℝ)*X 1 0+(870457669/2000000000 : ℝ)*X 1 1+(4352288397/10000000000 : ℝ)*X 1 2+(360900261/1000000000 : ℝ)*X 2 0+(870457669/2000000000 : ℝ)*X 2 1+(4352288397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66843/100000 : ℝ) ≤ (-579336139095090765646917836393799/866750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1351377/25000000000000 : ℝ)*(upper1) + (7467217/50000000000000 : ℝ)*(upper3) + (11469209/100000000000000 : ℝ)*(lower4) + (3338331/50000000000000 : ℝ)*(lower5) + (690944881828509/50000000000000 : ℝ)*(major0) + (690944881828509/50000000000000 : ℝ)*(major1) + (690944881828509/50000000000000 : ℝ)*(major2) + (139951153/100000000000000 : ℝ)*(sp3) + (1044547937898421/50000000000000 : ℝ)*(sp4) + (2089090664614787/100000000000000 : ℝ)*(sp5) + (1044545141353461/50000000000000 : ℝ)*(sp6) + (696963528452683/100000000000000 : ℝ)*(sp7) + (2605591027/50000000000000 : ℝ)*(sp13) + (5593089919/100000000000000 : ℝ)*(sp14) + (174240917100959/25000000000000 : ℝ)*(f.failure) + (1044547937898421/50000000000000 : ℝ)*(f.sum) + (32452684250061/17335000000000000000000000000 : ℝ)*base66 + (3653605198202749311/1733500000000000000000000000000000 : ℝ)*base67 + (9739237294608749311/1733500000000000000000000000000000 : ℝ)*base69 + (6751141077288749311/1733500000000000000000000000000000 : ℝ)*base71 + (21050639485011/17335000000000000000000000000 : ℝ)*base74 + (12558225447101249311/1733500000000000000000000000000000 : ℝ)*base75 + (14138496112261249311/1733500000000000000000000000000000 : ℝ)*base77 + (10207940312140249311/1733500000000000000000000000000000 : ℝ)*base79 + (72737002002237/8667500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2833589/500000000000000000000 : ℝ)*base89 + (2833589/500000000000000000000 : ℝ)*base91 + (2833589/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14659/25000 : ℝ) ≤ (254124959518421813817157887808761/433375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36552767/50000000000000 : ℝ)*(upper2) + (36889/39062500000 : ℝ)*(upper3) + (2939567/12500000000000 : ℝ)*(upper4) + (7914923/25000000000000 : ℝ)*(upper5) + (744801743784353/50000000000000 : ℝ)*(major0) + (744801743784353/50000000000000 : ℝ)*(major1) + (744801743784353/50000000000000 : ℝ)*(major2) + (2208368251189549/100000000000000 : ℝ)*(sp0) + (55208386159067/2500000000000 : ℝ)*(sp1) + (1104183751741679/50000000000000 : ℝ)*(sp2) + (751289674811363/100000000000000 : ℝ)*(sp3) + (17829798009/50000000000000 : ℝ)*(sp9) + (180123767/5000000000000 : ℝ)*(sp10) + (713692287/25000000000000 : ℝ)*(sp12) + (751289674811363/100000000000000 : ℝ)*(f.failure) + (2208371105958697/100000000000000 : ℝ)*(f.sum) + (129325402348127/17335000000000000000000000000 : ℝ)*base66 + (3001611632110444587/1733500000000000000000000000000000 : ℝ)*base67 + (3752819228619555413/1733500000000000000000000000000000 : ℝ)*base70 + (2557712732115055413/1733500000000000000000000000000000 : ℝ)*base72 + (827572309753/17335000000000000000000000000 : ℝ)*base73 + (1327329182979055413/1733500000000000000000000000000000 : ℝ)*base76 + (26330876859906055413/1733500000000000000000000000000000 : ℝ)*base78 + (2390709316571555413/1733500000000000000000000000000000 : ℝ)*base80 + (2633884981429/2166875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14309727/2000000000000000000000 : ℝ)*base90 + (14309727/2000000000000000000000 : ℝ)*base92 + (14309727/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (409/500 : ℝ) ≤ (28360954622948009659700314114923/34670000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61166417/100000000000000 : ℝ)*(upper0) + (5376461/12500000000000 : ℝ)*(upper1) + (24536299/20000000000000 : ℝ)*(upper3) + (6013249/2000000000000 : ℝ)*(upper4) + (30091308299221/2000000000000 : ℝ)*(major0) + (30091308299221/2000000000000 : ℝ)*(major1) + (30091308299221/2000000000000 : ℝ)*(major2) + (11059999319/100000000000000 : ℝ)*(sp1) + (36733027103/100000000000000 : ℝ)*(sp2) + (3049245763/25000000000000 : ℝ)*(sp3) + (1111513749156363/50000000000000 : ℝ)*(sp8) + (2223016438313407/100000000000000 : ℝ)*(sp9) + (2222990765285623/100000000000000 : ℝ)*(sp10) + (30352944313119/4000000000000 : ℝ)*(sp11) + (379417902405513/50000000000000 : ℝ)*(f.failure) + (1111513749156363/50000000000000 : ℝ)*(f.sum) + (8695272990293/3467000000000000000000000000 : ℝ)*base65 + (232404132711848359/69340000000000000000000000000000 : ℝ)*base67 + (612402046825611641/69340000000000000000000000000000 : ℝ)*base70 + (492289953533188359/69340000000000000000000000000000 : ℝ)*base71 + (12071305580801/3467000000000000000000000000 : ℝ)*base73 + (581116823522951641/69340000000000000000000000000000 : ℝ)*base76 + (131571763509228359/69340000000000000000000000000000 : ℝ)*base77 + (483916408675388359/69340000000000000000000000000000 : ℝ)*base79 + (17112561758929/1733500000000000000000000000 : ℝ)*base82 + (13950077/1000000000000000000000 : ℝ)*base90 + (13950077/1000000000000000000000 : ℝ)*base92 + (13950077/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-22641/25000 : ℝ) ≤ (-1569876290165197675078813251985413/1733500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17936417/100000000000000 : ℝ)*(lower0) + (33518319/100000000000000 : ℝ)*(lower1) + (21726169/100000000000000 : ℝ)*(lower2) + (1554883588921451/100000000000000 : ℝ)*(major0) + (1554883588921451/100000000000000 : ℝ)*(major1) + (1554883588921451/100000000000000 : ℝ)*(major2) + (845519261/100000000000000 : ℝ)*(sp0) + (14628895427/100000000000000 : ℝ)*(sp5) + (13485683647/100000000000000 : ℝ)*(sp6) + (468206261/25000000000000 : ℝ)*(sp7) + (1177869653516343/50000000000000 : ℝ)*(sp12) + (58893138091413/2500000000000 : ℝ)*(sp13) + (23557266668683/1000000000000 : ℝ)*(sp14) + (78421217852427/10000000000000 : ℝ)*(sp15) + (392107025674657/50000000000000 : ℝ)*(f.failure) + (1177870076275973/50000000000000 : ℝ)*(f.sum) + (5637275445929/34670000000000000000000000000 : ℝ)*base66 + (7568391666942378471/3467000000000000000000000000000000 : ℝ)*base68 + (18219305428401378471/3467000000000000000000000000000000 : ℝ)*base70 + (6190430783425621529/3467000000000000000000000000000000 : ℝ)*base71 + (103097160511739/34670000000000000000000000000 : ℝ)*base74 + (1330492123643378471/3467000000000000000000000000000000 : ℝ)*base76 + (3565796630487621529/3467000000000000000000000000000000 : ℝ)*base77 + (12201387569020378471/3467000000000000000000000000000000 : ℝ)*base80 + (103528646561471/34670000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1092853/1000000000000000000000 : ℝ)*base90 + (1092853/1000000000000000000000 : ℝ)*base92 + (1092853/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1720_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14659/25000 : ℝ) else (409/500 : ℝ) ≤ X j i ∧ X j i ≤ (22641/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1720_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1720_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14659/25000 : ℝ) else (409/500 : ℝ) ≤ X j i ∧ X j i ≤ (22641/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1720_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1720_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1720_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14659/25000 : ℝ) else (409/500 : ℝ) ≤ X j i ∧ X j i ≤ (22641/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1720_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
