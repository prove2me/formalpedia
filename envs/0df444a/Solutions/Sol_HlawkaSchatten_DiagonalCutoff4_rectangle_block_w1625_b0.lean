-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1625_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:04.850987+00:00
-- url     : https://prove2.me/submissions/01aafb1c-9a01-46cd-a4b7-76ab2bd1f3e8

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
theorem support_rectangle_w1625_s0_0 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-384389283/2500000000 : ℝ)*x 0 + (5817145227/10000000000 : ℝ)*x 1 + (4904044801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384389283/2500000000 : ℝ)^4819 ≤ (289911205941/3125000000000 : ℝ)^3795 := by
    have hnat : (384389283 : ℕ)^4819*3125000000000^3795 ≤ 289911205941^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384389283 2500000000 289911205941 3125000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5817145227/10000000000 : ℝ)^4819 ≤ (50259930179939/100000000000000 : ℝ)^3795 := by
    have hnat : (5817145227 : ℕ)^4819*100000000000000^3795 ≤ 50259930179939^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5817145227 10000000000 50259930179939 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4904044801/10000000000 : ℝ)^4819 ≤ (40462911217447/100000000000000 : ℝ)^3795 := by
    have hnat : (4904044801 : ℕ)^4819*100000000000000^3795 ≤ 40462911217447^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4904044801 10000000000 40462911217447 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384389283/2500000000 : ℝ), (5817145227/10000000000 : ℝ), (4904044801/10000000000 : ℝ)] ![(289911205941/3125000000000 : ℝ), (50259930179939/100000000000000 : ℝ), (40462911217447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384389283/2500000000 : ℝ)|^4819 ≤ (289911205941/3125000000000 : ℝ)^3795
        have hw : |(-384389283/2500000000 : ℝ)|=(384389283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5817145227/10000000000 : ℝ)|^4819 ≤ (50259930179939/100000000000000 : ℝ)^3795
        have hw : |(5817145227/10000000000 : ℝ)|=(5817145227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4904044801/10000000000 : ℝ)|^4819 ≤ (40462911217447/100000000000000 : ℝ)^3795
        have hw : |(4904044801/10000000000 : ℝ)|=(4904044801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s0_1 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170236761/312500000 : ℝ)*x 0 + (-2041436861/10000000000 : ℝ)*x 1 + (2452022849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170236761/312500000 : ℝ)^4819 ≤ (2890037139441/6250000000000 : ℝ)^3795 := by
    have hnat : (170236761 : ℕ)^4819*6250000000000^3795 ≤ 2890037139441^3795*312500000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170236761 312500000 2890037139441 6250000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2041436861/10000000000 : ℝ)^4819 ≤ (13296485129807/100000000000000 : ℝ)^3795 := by
    have hnat : (2041436861 : ℕ)^4819*100000000000000^3795 ≤ 13296485129807^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041436861 10000000000 13296485129807 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2452022849/5000000000 : ℝ)^4819 ≤ (316116567309/781250000000 : ℝ)^3795 := by
    have hnat : (2452022849 : ℕ)^4819*781250000000^3795 ≤ 316116567309^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452022849 5000000000 316116567309 781250000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170236761/312500000 : ℝ), (-2041436861/10000000000 : ℝ), (2452022849/5000000000 : ℝ)] ![(2890037139441/6250000000000 : ℝ), (13296485129807/100000000000000 : ℝ), (316116567309/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170236761/312500000 : ℝ)|^4819 ≤ (2890037139441/6250000000000 : ℝ)^3795
        have hw : |(170236761/312500000 : ℝ)|=(170236761/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2041436861/10000000000 : ℝ)|^4819 ≤ (13296485129807/100000000000000 : ℝ)^3795
        have hw : |(-2041436861/10000000000 : ℝ)|=(2041436861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2452022849/5000000000 : ℝ)|^4819 ≤ (316116567309/781250000000 : ℝ)^3795
        have hw : |(2452022849/5000000000 : ℝ)|=(2452022849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s0_2 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5447576129/10000000000 : ℝ)*x 0 + (613005653/1250000000 : ℝ)*x 1 + (-1020718877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5447576129/10000000000 : ℝ)^4819 ≤ (11560147956853/25000000000000 : ℝ)^3795 := by
    have hnat : (5447576129 : ℕ)^4819*25000000000000^3795 ≤ 11560147956853^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447576129 10000000000 11560147956853 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613005653/1250000000 : ℝ)^4819 ≤ (40462915649329/100000000000000 : ℝ)^3795 := by
    have hnat : (613005653 : ℕ)^4819*100000000000000^3795 ≤ 40462915649329^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613005653 1250000000 40462915649329 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020718877/5000000000 : ℝ)^4819 ≤ (13296492515607/100000000000000 : ℝ)^3795 := by
    have hnat : (1020718877 : ℕ)^4819*100000000000000^3795 ≤ 13296492515607^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020718877 5000000000 13296492515607 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5447576129/10000000000 : ℝ), (613005653/1250000000 : ℝ), (-1020718877/5000000000 : ℝ)] ![(11560147956853/25000000000000 : ℝ), (40462915649329/100000000000000 : ℝ), (13296492515607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5447576129/10000000000 : ℝ)|^4819 ≤ (11560147956853/25000000000000 : ℝ)^3795
        have hw : |(5447576129/10000000000 : ℝ)|=(5447576129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(613005653/1250000000 : ℝ)|^4819 ≤ (40462915649329/100000000000000 : ℝ)^3795
        have hw : |(613005653/1250000000 : ℝ)|=(613005653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020718877/5000000000 : ℝ)|^4819 ≤ (13296492515607/100000000000000 : ℝ)^3795
        have hw : |(-1020718877/5000000000 : ℝ)|=(1020718877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s0_3 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4102485921/10000000000 : ℝ)*x 0 + (1538501919/5000000000 : ℝ)*x 1 + (2682593189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4102485921/10000000000 : ℝ)^4819 ≤ (16128950051211/50000000000000 : ℝ)^3795 := by
    have hnat : (4102485921 : ℕ)^4819*50000000000000^3795 ≤ 16128950051211^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4102485921 10000000000 16128950051211 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1538501919/5000000000 : ℝ)^4819 ≤ (11193870670577/50000000000000 : ℝ)^3795 := by
    have hnat : (1538501919 : ℕ)^4819*50000000000000^3795 ≤ 11193870670577^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538501919 5000000000 11193870670577 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2682593189/5000000000 : ℝ)^4819 ≤ (45354358544539/100000000000000 : ℝ)^3795 := by
    have hnat : (2682593189 : ℕ)^4819*100000000000000^3795 ≤ 45354358544539^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682593189 5000000000 45354358544539 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4102485921/10000000000 : ℝ), (1538501919/5000000000 : ℝ), (2682593189/5000000000 : ℝ)] ![(16128950051211/50000000000000 : ℝ), (11193870670577/50000000000000 : ℝ), (45354358544539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4102485921/10000000000 : ℝ)|^4819 ≤ (16128950051211/50000000000000 : ℝ)^3795
        have hw : |(4102485921/10000000000 : ℝ)|=(4102485921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1538501919/5000000000 : ℝ)|^4819 ≤ (11193870670577/50000000000000 : ℝ)^3795
        have hw : |(1538501919/5000000000 : ℝ)|=(1538501919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2682593189/5000000000 : ℝ)|^4819 ≤ (45354358544539/100000000000000 : ℝ)^3795
        have hw : |(2682593189/5000000000 : ℝ)|=(2682593189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s0_4 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1540153327/10000000000 : ℝ)*x 0 + (4926989967/10000000000 : ℝ)*x 1 + (2896696429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540153327/10000000000 : ℝ)^4819 ≤ (2324263639333/25000000000000 : ℝ)^3795 := by
    have hnat : (1540153327 : ℕ)^4819*25000000000000^3795 ≤ 2324263639333^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540153327 10000000000 2324263639333 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4926989967/10000000000 : ℝ)^4819 ≤ (1628138613367/4000000000000 : ℝ)^3795 := by
    have hnat : (4926989967 : ℕ)^4819*4000000000000^3795 ≤ 1628138613367^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4926989967 10000000000 1628138613367 4000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2896696429/5000000000 : ℝ)^4819 ≤ (12499870023523/25000000000000 : ℝ)^3795 := by
    have hnat : (2896696429 : ℕ)^4819*25000000000000^3795 ≤ 12499870023523^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896696429 5000000000 12499870023523 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1540153327/10000000000 : ℝ), (4926989967/10000000000 : ℝ), (2896696429/5000000000 : ℝ)] ![(2324263639333/25000000000000 : ℝ), (1628138613367/4000000000000 : ℝ), (12499870023523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1540153327/10000000000 : ℝ)|^4819 ≤ (2324263639333/25000000000000 : ℝ)^3795
        have hw : |(-1540153327/10000000000 : ℝ)|=(1540153327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4926989967/10000000000 : ℝ)|^4819 ≤ (1628138613367/4000000000000 : ℝ)^3795
        have hw : |(4926989967/10000000000 : ℝ)|=(4926989967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2896696429/5000000000 : ℝ)|^4819 ≤ (12499870023523/25000000000000 : ℝ)^3795
        have hw : |(2896696429/5000000000 : ℝ)|=(2896696429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s0_5 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198249709/10000000000 : ℝ)*x 0 + (-576044793/5000000000 : ℝ)*x 1 + (2896696441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198249709/10000000000 : ℝ)^4819 ≤ (21784983579621/50000000000000 : ℝ)^3795 := by
    have hnat : (5198249709 : ℕ)^4819*50000000000000^3795 ≤ 21784983579621^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198249709 10000000000 21784983579621 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576044793/5000000000 : ℝ)^4819 ≤ (3215276229589/50000000000000 : ℝ)^3795 := by
    have hnat : (576044793 : ℕ)^4819*50000000000000^3795 ≤ 3215276229589^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576044793 5000000000 3215276229589 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2896696441/5000000000 : ℝ)^4819 ≤ (6249935044639/12500000000000 : ℝ)^3795 := by
    have hnat : (2896696441 : ℕ)^4819*12500000000000^3795 ≤ 6249935044639^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896696441 5000000000 6249935044639 12500000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198249709/10000000000 : ℝ), (-576044793/5000000000 : ℝ), (2896696441/5000000000 : ℝ)] ![(21784983579621/50000000000000 : ℝ), (3215276229589/50000000000000 : ℝ), (6249935044639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198249709/10000000000 : ℝ)|^4819 ≤ (21784983579621/50000000000000 : ℝ)^3795
        have hw : |(5198249709/10000000000 : ℝ)|=(5198249709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-576044793/5000000000 : ℝ)|^4819 ≤ (3215276229589/50000000000000 : ℝ)^3795
        have hw : |(-576044793/5000000000 : ℝ)|=(576044793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2896696441/5000000000 : ℝ)|^4819 ≤ (6249935044639/12500000000000 : ℝ)^3795
        have hw : |(2896696441/5000000000 : ℝ)|=(2896696441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s0_6 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599124893/5000000000 : ℝ)*x 0 + (724174113/1250000000 : ℝ)*x 1 + (-576044719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599124893/5000000000 : ℝ)^4819 ≤ (21784983989387/50000000000000 : ℝ)^3795 := by
    have hnat : (2599124893 : ℕ)^4819*50000000000000^3795 ≤ 21784983989387^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599124893 5000000000 21784983989387 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (724174113/1250000000 : ℝ)^4819 ≤ (24999740299107/50000000000000 : ℝ)^3795 := by
    have hnat : (724174113 : ℕ)^4819*50000000000000^3795 ≤ 24999740299107^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724174113 1250000000 24999740299107 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576044719/5000000000 : ℝ)^4819 ≤ (3215275705097/50000000000000 : ℝ)^3795 := by
    have hnat : (576044719 : ℕ)^4819*50000000000000^3795 ≤ 3215275705097^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576044719 5000000000 3215275705097 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599124893/5000000000 : ℝ), (724174113/1250000000 : ℝ), (-576044719/5000000000 : ℝ)] ![(21784983989387/50000000000000 : ℝ), (24999740299107/50000000000000 : ℝ), (3215275705097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599124893/5000000000 : ℝ)|^4819 ≤ (21784983989387/50000000000000 : ℝ)^3795
        have hw : |(2599124893/5000000000 : ℝ)|=(2599124893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(724174113/1250000000 : ℝ)|^4819 ≤ (24999740299107/50000000000000 : ℝ)^3795
        have hw : |(724174113/1250000000 : ℝ)|=(724174113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-576044719/5000000000 : ℝ)|^4819 ≤ (3215275705097/50000000000000 : ℝ)^3795
        have hw : |(-576044719/5000000000 : ℝ)|=(576044719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s0_7 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2054496697/5000000000 : ℝ)*x 0 + (5307684653/10000000000 : ℝ)*x 1 + (3136526879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054496697/5000000000 : ℝ)^4819 ≤ (646457780717/2000000000000 : ℝ)^3795 := by
    have hnat : (2054496697 : ℕ)^4819*2000000000000^3795 ≤ 646457780717^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054496697 5000000000 646457780717 2000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5307684653/10000000000 : ℝ)^4819 ≤ (44738004623609/100000000000000 : ℝ)^3795 := by
    have hnat : (5307684653 : ℕ)^4819*100000000000000^3795 ≤ 44738004623609^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5307684653 10000000000 44738004623609 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3136526879/10000000000 : ℝ)^4819 ≤ (22939106332443/100000000000000 : ℝ)^3795 := by
    have hnat : (3136526879 : ℕ)^4819*100000000000000^3795 ≤ 22939106332443^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136526879 10000000000 22939106332443 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2054496697/5000000000 : ℝ), (5307684653/10000000000 : ℝ), (3136526879/10000000000 : ℝ)] ![(646457780717/2000000000000 : ℝ), (44738004623609/100000000000000 : ℝ), (22939106332443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2054496697/5000000000 : ℝ)|^4819 ≤ (646457780717/2000000000000 : ℝ)^3795
        have hw : |(2054496697/5000000000 : ℝ)|=(2054496697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5307684653/10000000000 : ℝ)|^4819 ≤ (44738004623609/100000000000000 : ℝ)^3795
        have hw : |(5307684653/10000000000 : ℝ)|=(5307684653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3136526879/10000000000 : ℝ)|^4819 ≤ (22939106332443/100000000000000 : ℝ)^3795
        have hw : |(3136526879/10000000000 : ℝ)|=(3136526879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1625_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2171/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11951/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4815/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4815 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4815*1^1024 ≤ 0^1024*1^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4815/1024 : ℝ) ≤ (134532437208042193/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4815 ≤ (134532437208042193/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4815*10000000000000000000^1024 ≤ 134532437208042193^1024*5^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 134532437208042193 10000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (134532437208042193/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4815 := by
      have hnat : (1 : ℕ)^1024*1^4815 ≤ 1^4815*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10134532437208042193/10000000000000000000 : ℝ) ≤ (2507115130574231/2500000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (10134532437208042193/10000000000000000000 : ℝ)^1024 ≤ (2507115130574231/2500000000000000 : ℝ)^4815 := by
      have hnat : (10134532437208042193 : ℕ)^1024*2500000000000000^4815 ≤ 2507115130574231^4815*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10134532437208042193 10000000000000000000 2507115130574231 2500000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507115130574231/2500000000000000 : ℝ)) (X := (10134532437208042193/10000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5134532437208042193/5000000000000000000 : ℝ) ≤ (1257115130574231/1250000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (5134532437208042193/5000000000000000000 : ℝ)^1024 ≤ (1257115130574231/1250000000000000 : ℝ)^4815 := by
      have hnat : (5134532437208042193 : ℕ)^1024*1250000000000000^4815 ≤ 1257115130574231^4815*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5134532437208042193 5000000000000000000 1257115130574231 1250000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257115130574231/1250000000000000 : ℝ)) (X := (5134532437208042193/5000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7115130574231/1000000000000000 : ℝ)*(0 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7115130574231/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(134532437208042193/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7115130574231/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4815/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7115130574231/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2507115130574231/2500000000000000 : ℝ) by norm_num, show 1+(134532437208042193/10000000000000000000 : ℝ)+(0 : ℝ)=(10134532437208042193/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(134532437208042193/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7115130574231/1000000000000000 : ℝ)*(2/5 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7115130574231/1000000000000000 : ℝ)*(2/5 : ℝ)=(1257115130574231/1250000000000000 : ℝ) by norm_num, show 1+2*(134532437208042193/10000000000000000000 : ℝ)=(5134532437208042193/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7115130574231/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7115130574231/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7115130574231/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7115130574231/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7115130574231/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7115130574231/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-384389283/2500000000 : ℝ)*X 0 0+(5817145227/10000000000 : ℝ)*X 0 1+(4904044801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((170236761/312500000 : ℝ)*X 1 0+(-2041436861/10000000000 : ℝ)*X 1 1+(2452022849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5447576129/10000000000 : ℝ)*X 2 0+(613005653/1250000000 : ℝ)*X 2 1+(-1020718877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4102485921/10000000000 : ℝ)*X 0 0+(1538501919/5000000000 : ℝ)*X 0 1+(2682593189/5000000000 : ℝ)*X 0 2+(4102485921/10000000000 : ℝ)*X 1 0+(1538501919/5000000000 : ℝ)*X 1 1+(2682593189/5000000000 : ℝ)*X 1 2+(4102485921/10000000000 : ℝ)*X 2 0+(1538501919/5000000000 : ℝ)*X 2 1+(2682593189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1540153327/10000000000 : ℝ)*X 0 0+(4926989967/10000000000 : ℝ)*X 0 1+(2896696429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198249709/10000000000 : ℝ)*X 1 0+(-576044793/5000000000 : ℝ)*X 1 1+(2896696441/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599124893/5000000000 : ℝ)*X 2 0+(724174113/1250000000 : ℝ)*X 2 1+(-576044719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2054496697/5000000000 : ℝ)*X 0 0+(5307684653/10000000000 : ℝ)*X 0 1+(3136526879/10000000000 : ℝ)*X 0 2+(2054496697/5000000000 : ℝ)*X 1 0+(5307684653/10000000000 : ℝ)*X 1 1+(3136526879/10000000000 : ℝ)*X 1 2+(2054496697/5000000000 : ℝ)*X 2 0+(5307684653/10000000000 : ℝ)*X 2 1+(3136526879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23650404524032231468131/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1378531/25000000000000 : ℝ)*(base16) + (159407121/25000000000000 : ℝ)*(base19) + (347638123/50000000000000 : ℝ)*(base23) + (52822619/100000000000000 : ℝ)*(upper2) + (204335869/100000000000000 : ℝ)*(upper3) + (383051981293533/50000000000000 : ℝ)*(major0) + (383051981293533/50000000000000 : ℝ)*(major1) + (383051981293533/50000000000000 : ℝ)*(major2) + (136896764326243/12500000000000 : ℝ)*(sp0) + (219035180334619/20000000000000 : ℝ)*(sp1) + (1095175849539457/100000000000000 : ℝ)*(sp2) + (218514672678519/50000000000000 : ℝ)*(sp3) + (2430205759/100000000000000 : ℝ)*(sp4) + (1908865897/100000000000000 : ℝ)*(sp7) + (87406250844587/20000000000000 : ℝ)*(f.failure) + (1095176544815703/100000000000000 : ℝ)*(f.sum) + (24885933626877/25000000000000000000000000000 : ℝ)*base66 + (48062065448123/50000000000000000000000000000 : ℝ)*base67 + (185317247098123/50000000000000000000000000000 : ℝ)*base69 + (103984663948123/50000000000000000000000000000 : ℝ)*base71 + (81641061998123/25000000000000000000000000000 : ℝ)*base73 + (142320999898123/50000000000000000000000000000 : ℝ)*base75 + (1976038298123/50000000000000000000000000000 : ℝ)*base77 + (165289759098123/50000000000000000000000000000 : ℝ)*base79 + (99261600523123/25000000000000000000000000000 : ℝ)*base81 + (2176211/1000000000000000000000 : ℝ)*base90 + (2176211/1000000000000000000000 : ℝ)*base92 + (2176211/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (196216355717954812142577/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1737208151/100000000000000 : ℝ)*(base19) + (1769311177/100000000000000 : ℝ)*(base23) + (16976357/20000000000000 : ℝ)*(base32) + (10646183/4000000000000 : ℝ)*(upper3) + (46955093/20000000000000 : ℝ)*(upper5) + (807390518855389/100000000000000 : ℝ)*(major0) + (807390518855389/100000000000000 : ℝ)*(major1) + (807390518855389/100000000000000 : ℝ)*(major2) + (2627717973/50000000000000 : ℝ)*(sp1) + (5568311329/100000000000000 : ℝ)*(sp2) + (1154197215195327/100000000000000 : ℝ)*(sp4) + (1154190222551229/100000000000000 : ℝ)*(sp5) + (1154189877572821/100000000000000 : ℝ)*(sp6) + (460583476011853/100000000000000 : ℝ)*(sp7) + (230291780446819/50000000000000 : ℝ)*(f.failure) + (1154197215195327/100000000000000 : ℝ)*(f.sum) + (28528611230859/50000000000000000000000000000 : ℝ)*base65 + (979879202919141/100000000000000000000000000000 : ℝ)*base68 + (308418716419141/100000000000000000000000000000 : ℝ)*base70 + (37979375380859/100000000000000000000000000000 : ℝ)*base71 + (378180846569141/50000000000000000000000000000 : ℝ)*base74 + (536777511580859/100000000000000000000000000000 : ℝ)*base75 + (701634664019141/100000000000000000000000000000 : ℝ)*base78 + (237671270019141/100000000000000000000000000000 : ℝ)*base80 + (64062437269141/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (15803893/2500000000000000000000 : ℝ)*base89 + (15803893/2500000000000000000000 : ℝ)*base91 + (15803893/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1625_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11951/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1625_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1625_s1_0 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-66166141/400000000 : ℝ)*x 0 + (5516404963/10000000000 : ℝ)*x 1 + (1025847949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66166141/400000000 : ℝ)^4819 ≤ (5089734516037/50000000000000 : ℝ)^3795 := by
    have hnat : (66166141 : ℕ)^4819*50000000000000^3795 ≤ 5089734516037^3795*400000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66166141 400000000 5089734516037 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516404963/10000000000 : ℝ)^4819 ≤ (11745933987253/25000000000000 : ℝ)^3795 := by
    have hnat : (5516404963 : ℕ)^4819*25000000000000^3795 ≤ 11745933987253^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516404963 10000000000 11745933987253 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025847949/2000000000 : ℝ)^4819 ≤ (21418397504853/50000000000000 : ℝ)^3795 := by
    have hnat : (1025847949 : ℕ)^4819*50000000000000^3795 ≤ 21418397504853^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025847949 2000000000 21418397504853 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66166141/400000000 : ℝ), (5516404963/10000000000 : ℝ), (1025847949/2000000000 : ℝ)] ![(5089734516037/50000000000000 : ℝ), (11745933987253/25000000000000 : ℝ), (21418397504853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66166141/400000000 : ℝ)|^4819 ≤ (5089734516037/50000000000000 : ℝ)^3795
        have hw : |(-66166141/400000000 : ℝ)|=(66166141/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516404963/10000000000 : ℝ)|^4819 ≤ (11745933987253/25000000000000 : ℝ)^3795
        have hw : |(5516404963/10000000000 : ℝ)|=(5516404963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025847949/2000000000 : ℝ)|^4819 ≤ (21418397504853/50000000000000 : ℝ)^3795
        have hw : |(1025847949/2000000000 : ℝ)|=(1025847949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s1_1 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536757599/1000000000 : ℝ)*x 0 + (-1856147423/10000000000 : ℝ)*x 1 + (641154941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536757599/1000000000 : ℝ)^4819 ≤ (11345002807637/25000000000000 : ℝ)^3795 := by
    have hnat : (536757599 : ℕ)^4819*25000000000000^3795 ≤ 11345002807637^3795*1000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536757599 1000000000 11345002807637 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1856147423/10000000000 : ℝ)^4819 ≤ (11783196043861/100000000000000 : ℝ)^3795 := by
    have hnat : (1856147423 : ℕ)^4819*100000000000000^3795 ≤ 11783196043861^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856147423 10000000000 11783196043861 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641154941/1250000000 : ℝ)^4819 ≤ (4283679270843/10000000000000 : ℝ)^3795 := by
    have hnat : (641154941 : ℕ)^4819*10000000000000^3795 ≤ 4283679270843^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641154941 1250000000 4283679270843 10000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536757599/1000000000 : ℝ), (-1856147423/10000000000 : ℝ), (641154941/1250000000 : ℝ)] ![(11345002807637/25000000000000 : ℝ), (11783196043861/100000000000000 : ℝ), (4283679270843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536757599/1000000000 : ℝ)|^4819 ≤ (11345002807637/25000000000000 : ℝ)^3795
        have hw : |(536757599/1000000000 : ℝ)|=(536757599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1856147423/10000000000 : ℝ)|^4819 ≤ (11783196043861/100000000000000 : ℝ)^3795
        have hw : |(-1856147423/10000000000 : ℝ)|=(1856147423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641154941/1250000000 : ℝ)|^4819 ≤ (4283679270843/10000000000000 : ℝ)^3795
        have hw : |(641154941/1250000000 : ℝ)|=(641154941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s1_2 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134189411/250000000 : ℝ)*x 0 + (641154867/1250000000 : ℝ)*x 1 + (-1856147603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134189411/250000000 : ℝ)^4819 ≤ (22690008030813/50000000000000 : ℝ)^3795 := by
    have hnat : (134189411 : ℕ)^4819*50000000000000^3795 ≤ 22690008030813^3795*250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134189411 250000000 22690008030813 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641154867/1250000000 : ℝ)^4819 ≤ (10709196607573/25000000000000 : ℝ)^3795 := by
    have hnat : (641154867 : ℕ)^4819*25000000000000^3795 ≤ 10709196607573^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641154867 1250000000 10709196607573 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856147603/10000000000 : ℝ)^4819 ≤ (736449843429/6250000000000 : ℝ)^3795 := by
    have hnat : (1856147603 : ℕ)^4819*6250000000000^3795 ≤ 736449843429^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856147603 10000000000 736449843429 6250000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134189411/250000000 : ℝ), (641154867/1250000000 : ℝ), (-1856147603/10000000000 : ℝ)] ![(22690008030813/50000000000000 : ℝ), (10709196607573/25000000000000 : ℝ), (736449843429/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134189411/250000000 : ℝ)|^4819 ≤ (22690008030813/50000000000000 : ℝ)^3795
        have hw : |(134189411/250000000 : ℝ)|=(134189411/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641154867/1250000000 : ℝ)|^4819 ≤ (10709196607573/25000000000000 : ℝ)^3795
        have hw : |(641154867/1250000000 : ℝ)|=(641154867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1856147603/10000000000 : ℝ)|^4819 ≤ (736449843429/6250000000000 : ℝ)^3795
        have hw : |(-1856147603/10000000000 : ℝ)|=(1856147603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s1_3 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095364987/5000000000 : ℝ)*x 0 + (58229651/156250000 : ℝ)*x 1 + (4696914327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095364987/5000000000 : ℝ)^4819 ≤ (16570766180741/50000000000000 : ℝ)^3795 := by
    have hnat : (2095364987 : ℕ)^4819*50000000000000^3795 ≤ 16570766180741^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095364987 5000000000 16570766180741 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58229651/156250000 : ℝ)^4819 ≤ (28553221042547/100000000000000 : ℝ)^3795 := by
    have hnat : (58229651 : ℕ)^4819*100000000000000^3795 ≤ 28553221042547^3795*156250000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58229651 156250000 28553221042547 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4696914327/10000000000 : ℝ)^4819 ≤ (38305246576587/100000000000000 : ℝ)^3795 := by
    have hnat : (4696914327 : ℕ)^4819*100000000000000^3795 ≤ 38305246576587^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696914327 10000000000 38305246576587 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095364987/5000000000 : ℝ), (58229651/156250000 : ℝ), (4696914327/10000000000 : ℝ)] ![(16570766180741/50000000000000 : ℝ), (28553221042547/100000000000000 : ℝ), (38305246576587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095364987/5000000000 : ℝ)|^4819 ≤ (16570766180741/50000000000000 : ℝ)^3795
        have hw : |(2095364987/5000000000 : ℝ)|=(2095364987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(58229651/156250000 : ℝ)|^4819 ≤ (28553221042547/100000000000000 : ℝ)^3795
        have hw : |(58229651/156250000 : ℝ)|=(58229651/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4696914327/10000000000 : ℝ)|^4819 ≤ (38305246576587/100000000000000 : ℝ)^3795
        have hw : |(4696914327/10000000000 : ℝ)|=(4696914327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s1_4 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1654347793/10000000000 : ℝ)*x 0 + (160416797/312500000 : ℝ)*x 1 + (689030707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1654347793/10000000000 : ℝ)^4819 ≤ (5090493569929/50000000000000 : ℝ)^3795 := by
    have hnat : (1654347793 : ℕ)^4819*50000000000000^3795 ≤ 5090493569929^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654347793 10000000000 5090493569929 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160416797/312500000 : ℝ)^4819 ≤ (42880256271233/100000000000000 : ℝ)^3795 := by
    have hnat : (160416797 : ℕ)^4819*100000000000000^3795 ≤ 42880256271233^3795*312500000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160416797 312500000 42880256271233 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689030707/1250000000 : ℝ)^4819 ≤ (46938756581819/100000000000000 : ℝ)^3795 := by
    have hnat : (689030707 : ℕ)^4819*100000000000000^3795 ≤ 46938756581819^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689030707 1250000000 46938756581819 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1654347793/10000000000 : ℝ), (160416797/312500000 : ℝ), (689030707/1250000000 : ℝ)] ![(5090493569929/50000000000000 : ℝ), (42880256271233/100000000000000 : ℝ), (46938756581819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1654347793/10000000000 : ℝ)|^4819 ≤ (5090493569929/50000000000000 : ℝ)^3795
        have hw : |(-1654347793/10000000000 : ℝ)|=(1654347793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160416797/312500000 : ℝ)|^4819 ≤ (42880256271233/100000000000000 : ℝ)^3795
        have hw : |(160416797/312500000 : ℝ)|=(160416797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689030707/1250000000 : ℝ)|^4819 ≤ (46938756581819/100000000000000 : ℝ)^3795
        have hw : |(689030707/1250000000 : ℝ)|=(689030707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s1_5 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264360591/10000000000 : ℝ)*x 0 + (-294628117/2000000000 : ℝ)*x 1 + (1378061499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264360591/10000000000 : ℝ)^4819 ≤ (11068701747537/25000000000000 : ℝ)^3795 := by
    have hnat : (5264360591 : ℕ)^4819*25000000000000^3795 ≤ 11068701747537^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264360591 10000000000 11068701747537 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294628117/2000000000 : ℝ)^4819 ≤ (4393216365953/50000000000000 : ℝ)^3795 := by
    have hnat : (294628117 : ℕ)^4819*50000000000000^3795 ≤ 4393216365953^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294628117 2000000000 4393216365953 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378061499/2500000000 : ℝ)^4819 ≤ (2933672516141/6250000000000 : ℝ)^3795 := by
    have hnat : (1378061499 : ℕ)^4819*6250000000000^3795 ≤ 2933672516141^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378061499 2500000000 2933672516141 6250000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264360591/10000000000 : ℝ), (-294628117/2000000000 : ℝ), (1378061499/2500000000 : ℝ)] ![(11068701747537/25000000000000 : ℝ), (4393216365953/50000000000000 : ℝ), (2933672516141/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264360591/10000000000 : ℝ)|^4819 ≤ (11068701747537/25000000000000 : ℝ)^3795
        have hw : |(5264360591/10000000000 : ℝ)|=(5264360591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294628117/2000000000 : ℝ)|^4819 ≤ (4393216365953/50000000000000 : ℝ)^3795
        have hw : |(-294628117/2000000000 : ℝ)|=(294628117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378061499/2500000000 : ℝ)|^4819 ≤ (2933672516141/6250000000000 : ℝ)^3795
        have hw : |(1378061499/2500000000 : ℝ)|=(1378061499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s1_6 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632179971/5000000000 : ℝ)*x 0 + (5512246237/10000000000 : ℝ)*x 1 + (-1473141157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632179971/5000000000 : ℝ)^4819 ≤ (11068700014767/25000000000000 : ℝ)^3795 := by
    have hnat : (2632179971 : ℕ)^4819*25000000000000^3795 ≤ 11068700014767^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632179971 5000000000 11068700014767 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512246237/10000000000 : ℝ)^4819 ≤ (234693814321/500000000000 : ℝ)^3795 := by
    have hnat : (5512246237 : ℕ)^4819*500000000000^3795 ≤ 234693814321^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512246237 10000000000 234693814321 500000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1473141157/10000000000 : ℝ)^4819 ≤ (2196609266029/25000000000000 : ℝ)^3795 := by
    have hnat : (1473141157 : ℕ)^4819*25000000000000^3795 ≤ 2196609266029^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473141157 10000000000 2196609266029 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632179971/5000000000 : ℝ), (5512246237/10000000000 : ℝ), (-1473141157/10000000000 : ℝ)] ![(11068700014767/25000000000000 : ℝ), (234693814321/500000000000 : ℝ), (2196609266029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632179971/5000000000 : ℝ)|^4819 ≤ (11068700014767/25000000000000 : ℝ)^3795
        have hw : |(2632179971/5000000000 : ℝ)|=(2632179971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512246237/10000000000 : ℝ)|^4819 ≤ (234693814321/500000000000 : ℝ)^3795
        have hw : |(5512246237/10000000000 : ℝ)|=(5512246237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1473141157/10000000000 : ℝ)|^4819 ≤ (2196609266029/25000000000000 : ℝ)^3795
        have hw : |(-1473141157/10000000000 : ℝ)|=(1473141157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s1_7 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095607191/5000000000 : ℝ)*x 0 + (4686646493/10000000000 : ℝ)*x 1 + (3737119839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095607191/5000000000 : ℝ)^4819 ≤ (33146396950243/100000000000000 : ℝ)^3795 := by
    have hnat : (2095607191 : ℕ)^4819*100000000000000^3795 ≤ 33146396950243^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095607191 5000000000 33146396950243 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4686646493/10000000000 : ℝ)^4819 ≤ (19099472288559/50000000000000 : ℝ)^3795 := by
    have hnat : (4686646493 : ℕ)^4819*50000000000000^3795 ≤ 19099472288559^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4686646493 10000000000 19099472288559 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3737119839/10000000000 : ℝ)^4819 ≤ (28654658457407/100000000000000 : ℝ)^3795 := by
    have hnat : (3737119839 : ℕ)^4819*100000000000000^3795 ≤ 28654658457407^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3737119839 10000000000 28654658457407 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095607191/5000000000 : ℝ), (4686646493/10000000000 : ℝ), (3737119839/10000000000 : ℝ)] ![(33146396950243/100000000000000 : ℝ), (19099472288559/50000000000000 : ℝ), (28654658457407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095607191/5000000000 : ℝ)|^4819 ≤ (33146396950243/100000000000000 : ℝ)^3795
        have hw : |(2095607191/5000000000 : ℝ)|=(2095607191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4686646493/10000000000 : ℝ)|^4819 ≤ (19099472288559/50000000000000 : ℝ)^3795
        have hw : |(4686646493/10000000000 : ℝ)|=(4686646493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3737119839/10000000000 : ℝ)|^4819 ≤ (28654658457407/100000000000000 : ℝ)^3795
        have hw : |(3737119839/10000000000 : ℝ)|=(3737119839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1625_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4693/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8799/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11951/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11951/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11951/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11951/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11951/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11951/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2171/50000 : ℝ) ^ (4815/1024 : ℝ) ≤ (19641982325451/50000000000000000000 : ℝ) := by
    have hpowers : (2171/50000 : ℝ)^4815 ≤ (19641982325451/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2171 : ℕ)^4815*50000000000000000000^1024 ≤ 19641982325451^1024*50000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2171 50000 19641982325451 50000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2171/50000 : ℝ)) (X := (19641982325451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11951/50000 : ℝ) ^ (4815/1024 : ℝ) ≤ (119482841558112071/100000000000000000000 : ℝ) := by
    have hpowers : (11951/50000 : ℝ)^4815 ≤ (119482841558112071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11951 : ℕ)^4815*100000000000000000000^1024 ≤ 119482841558112071^1024*50000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11951 50000 119482841558112071 100000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11951/50000 : ℝ)) (X := (119482841558112071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000019641982325451/25000000000000000000 : ℝ) ≤ (2500000417723441/2500000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (25000019641982325451/25000000000000000000 : ℝ)^1024 ≤ (2500000417723441/2500000000000000 : ℝ)^4815 := by
      have hnat : (25000019641982325451 : ℕ)^1024*2500000000000000^4815 ≤ 2500000417723441^4815*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000019641982325451 25000000000000000000 2500000417723441 2500000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000417723441/2500000000000000 : ℝ)) (X := (25000019641982325451/25000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100119522125522762973/100000000000000000000 : ℝ) ≤ (5001270333442981/5000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (100119522125522762973/100000000000000000000 : ℝ)^1024 ≤ (5001270333442981/5000000000000000 : ℝ)^4815 := by
      have hnat : (100119522125522762973 : ℕ)^1024*5000000000000000^4815 ≤ 5001270333442981^4815*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100119522125522762973 100000000000000000000 5001270333442981 5000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001270333442981/5000000000000000 : ℝ)) (X := (100119522125522762973/100000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50119482841558112071/50000000000000000000 : ℝ) ≤ (125063495785977/125000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50119482841558112071/50000000000000000000 : ℝ)^1024 ≤ (125063495785977/125000000000000 : ℝ)^4815 := by
      have hnat : (50119482841558112071 : ℕ)^1024*125000000000000^4815 ≤ 125063495785977^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50119482841558112071 50000000000000000000 125063495785977 125000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125063495785977/125000000000000 : ℝ)) (X := (50119482841558112071/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19641982325451/50000000000000000000 : ℝ) ≤ ((24447248005185722051/24450000000000000000 : ℝ)+2*(1269497996099/978000000000000 : ℝ)*(2171/50000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (24447248005185722051/24450000000000000000 : ℝ)+2*(1269497996099/978000000000000 : ℝ)*(2171/50000 : ℝ)=(2500000417723441/2500000000000000 : ℝ) by norm_num, show 1+2*(19641982325451/50000000000000000000 : ℝ)=(25000019641982325451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(119482841558112071/100000000000000000000 : ℝ)+(19641982325451/50000000000000000000 : ℝ) ≤ ((24447248005185722051/24450000000000000000 : ℝ)+(1269497996099/978000000000000 : ℝ)*((11951/50000 : ℝ)+(2171/50000 : ℝ)))^(4815/1024 : ℝ) := by
    rw [show (24447248005185722051/24450000000000000000 : ℝ)+(1269497996099/978000000000000 : ℝ)*((11951/50000 : ℝ)+(2171/50000 : ℝ))=(5001270333442981/5000000000000000 : ℝ) by norm_num, show 1+(119482841558112071/100000000000000000000 : ℝ)+(19641982325451/50000000000000000000 : ℝ)=(100119522125522762973/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(119482841558112071/100000000000000000000 : ℝ) ≤ ((24447248005185722051/24450000000000000000 : ℝ)+2*(1269497996099/978000000000000 : ℝ)*(11951/50000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (24447248005185722051/24450000000000000000 : ℝ)+2*(1269497996099/978000000000000 : ℝ)*(11951/50000 : ℝ)=(125063495785977/125000000000000 : ℝ) by norm_num, show 1+2*(119482841558112071/100000000000000000000 : ℝ)=(50119482841558112071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24447248005185722051/24450000000000000000 : ℝ)*(X 1 0+X 2 0)+(1269497996099/978000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (2171/50000 : ℝ)) (hi := (11951/50000 : ℝ)) (c := (24447248005185722051/24450000000000000000 : ℝ)) (alpha := (1269497996099/978000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24447248005185722051/24450000000000000000 : ℝ)*(X 0 1+X 2 1)+(1269497996099/978000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (2171/50000 : ℝ)) (hi := (11951/50000 : ℝ)) (c := (24447248005185722051/24450000000000000000 : ℝ)) (alpha := (1269497996099/978000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24447248005185722051/24450000000000000000 : ℝ)*(X 0 2+X 1 2)+(1269497996099/978000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (2171/50000 : ℝ)) (hi := (11951/50000 : ℝ)) (c := (24447248005185722051/24450000000000000000 : ℝ)) (alpha := (1269497996099/978000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66166141/400000000 : ℝ)*X 0 0+(5516404963/10000000000 : ℝ)*X 0 1+(1025847949/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((536757599/1000000000 : ℝ)*X 1 0+(-1856147423/10000000000 : ℝ)*X 1 1+(641154941/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134189411/250000000 : ℝ)*X 2 0+(641154867/1250000000 : ℝ)*X 2 1+(-1856147603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2095364987/5000000000 : ℝ)*X 0 0+(58229651/156250000 : ℝ)*X 0 1+(4696914327/10000000000 : ℝ)*X 0 2+(2095364987/5000000000 : ℝ)*X 1 0+(58229651/156250000 : ℝ)*X 1 1+(4696914327/10000000000 : ℝ)*X 1 2+(2095364987/5000000000 : ℝ)*X 2 0+(58229651/156250000 : ℝ)*X 2 1+(4696914327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1654347793/10000000000 : ℝ)*X 0 0+(160416797/312500000 : ℝ)*X 0 1+(689030707/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264360591/10000000000 : ℝ)*X 1 0+(-294628117/2000000000 : ℝ)*X 1 1+(1378061499/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632179971/5000000000 : ℝ)*X 2 0+(5512246237/10000000000 : ℝ)*X 2 1+(-1473141157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2095607191/5000000000 : ℝ)*X 0 0+(4686646493/10000000000 : ℝ)*X 0 1+(3737119839/10000000000 : ℝ)*X 0 2+(2095607191/5000000000 : ℝ)*X 1 0+(4686646493/10000000000 : ℝ)*X 1 1+(3737119839/10000000000 : ℝ)*X 1 2+(2095607191/5000000000 : ℝ)*X 2 0+(4686646493/10000000000 : ℝ)*X 2 1+(3737119839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1665828156029836003940922441/203750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73635289/20000000000000 : ℝ)*(base1) + (172260161/12500000000000 : ℝ)*(base19) + (1594622117/100000000000000 : ℝ)*(base23) + (190647901/100000000000000 : ℝ)*(upper3) + (24007293/20000000000000 : ℝ)*(upper5) + (1806796839113391/100000000000000 : ℝ)*(major0) + (1806796839113391/100000000000000 : ℝ)*(major1) + (1806796839113391/100000000000000 : ℝ)*(major2) + (645720816933073/25000000000000 : ℝ)*(sp0) + (32286095938677/1250000000000 : ℝ)*(sp1) + (645721864638333/25000000000000 : ℝ)*(sp2) + (1030700430038233/100000000000000 : ℝ)*(sp3) + (3076809801/50000000000000 : ℝ)*(sp4) + (888577131/25000000000000 : ℝ)*(sp7) + (644190220327/62500000000 : ℝ)*(f.failure) + (2582889053175449/100000000000000 : ℝ)*(f.sum) + (2942497357297/16300000000000000000000000000 : ℝ)*base66 + (4514976532273063353/815000000000000000000000000000000 : ℝ)*base68 + (4466446241538063353/815000000000000000000000000000000 : ℝ)*base70 + (433288529803063353/815000000000000000000000000000000 : ℝ)*base72 + (23730277579297/16300000000000000000000000000 : ℝ)*base74 + (4786524205641936647/815000000000000000000000000000000 : ℝ)*base75 + (6237294469003063353/815000000000000000000000000000000 : ℝ)*base78 + (510568692893063353/815000000000000000000000000000000 : ℝ)*base80 + (31149144868603/16300000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (21181/3125000000000000000 : ℝ)*base90 + (21181/3125000000000000000 : ℝ)*base92 + (21181/3125000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (614327957943139258928207211/203750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (759657049/100000000000000 : ℝ)*(base19) + (530885511/100000000000000 : ℝ)*(base23) + (64192891/100000000000000 : ℝ)*(upper2) + (46000593/25000000000000 : ℝ)*(upper3) + (1846157494544661/100000000000000 : ℝ)*(major0) + (1846157494544661/100000000000000 : ℝ)*(major1) + (1846157494544661/100000000000000 : ℝ)*(major2) + (6439691723/100000000000000 : ℝ)*(sp1) + (2573343617/50000000000000 : ℝ)*(sp2) + (116007159/20000000000000 : ℝ)*(sp3) + (2639156877746953/100000000000000 : ℝ)*(sp4) + (1319574839199091/50000000000000 : ℝ)*(sp5) + (20618368751361/781250000000 : ℝ)*(sp6) + (131644678850377/12500000000000 : ℝ)*(sp7) + (105315801083881/10000000000000 : ℝ)*(f.failure) + (2639156877746953/100000000000000 : ℝ)*(f.sum) + (4083016196087/16300000000000000000000000000 : ℝ)*base66 + (5780276449304001763/815000000000000000000000000000000 : ℝ)*base68 + (1409695898059001763/815000000000000000000000000000000 : ℝ)*base70 + (9581306614914001763/815000000000000000000000000000000 : ℝ)*base72 + (21332307918887/16300000000000000000000000000 : ℝ)*base74 + (5833287574179001763/815000000000000000000000000000000 : ℝ)*base76 + (1355531635425998237/815000000000000000000000000000000 : ℝ)*base77 + (3321236450824001763/815000000000000000000000000000000 : ℝ)*base80 + (41392410859487/16300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1840993/500000000000000000000 : ℝ)*base90 + (1840993/500000000000000000000 : ℝ)*base92 + (1840993/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1625_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8799/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1625_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1625_s2_0 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-416532597/2500000000 : ℝ)*x 0 + (1365126563/2500000000 : ℝ)*x 1 + (5177274317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416532597/2500000000 : ℝ)^4819 ≤ (513657601987/5000000000000 : ℝ)^3795 := by
    have hnat : (416532597 : ℕ)^4819*5000000000000^3795 ≤ 513657601987^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416532597 2500000000 513657601987 5000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365126563/2500000000 : ℝ)^4819 ≤ (362343796681/781250000000 : ℝ)^3795 := by
    have hnat : (1365126563 : ℕ)^4819*781250000000^3795 ≤ 362343796681^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365126563 2500000000 362343796681 781250000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177274317/10000000000 : ℝ)^4819 ≤ (21673420984581/50000000000000 : ℝ)^3795 := by
    have hnat : (5177274317 : ℕ)^4819*50000000000000^3795 ≤ 21673420984581^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177274317 10000000000 21673420984581 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416532597/2500000000 : ℝ), (1365126563/2500000000 : ℝ), (5177274317/10000000000 : ℝ)] ![(513657601987/5000000000000 : ℝ), (362343796681/781250000000 : ℝ), (21673420984581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416532597/2500000000 : ℝ)|^4819 ≤ (513657601987/5000000000000 : ℝ)^3795
        have hw : |(-416532597/2500000000 : ℝ)|=(416532597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365126563/2500000000 : ℝ)|^4819 ≤ (362343796681/781250000000 : ℝ)^3795
        have hw : |(1365126563/2500000000 : ℝ)|=(1365126563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177274317/10000000000 : ℝ)|^4819 ≤ (21673420984581/50000000000000 : ℝ)^3795
        have hw : |(5177274317/10000000000 : ℝ)|=(5177274317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s2_1 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352917197/10000000000 : ℝ)*x 0 + (-90612449/500000000 : ℝ)*x 1 + (5177274393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352917197/10000000000 : ℝ)^4819 ≤ (22611348211381/50000000000000 : ℝ)^3795 := by
    have hnat : (5352917197 : ℕ)^4819*50000000000000^3795 ≤ 22611348211381^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352917197 10000000000 22611348211381 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90612449/500000000 : ℝ)^4819 ≤ (11430460789883/100000000000000 : ℝ)^3795 := by
    have hnat : (90612449 : ℕ)^4819*100000000000000^3795 ≤ 11430460789883^3795*500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90612449 500000000 11430460789883 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177274393/10000000000 : ℝ)^4819 ≤ (2709177673573/6250000000000 : ℝ)^3795 := by
    have hnat : (5177274393 : ℕ)^4819*6250000000000^3795 ≤ 2709177673573^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177274393 10000000000 2709177673573 6250000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352917197/10000000000 : ℝ), (-90612449/500000000 : ℝ), (5177274393/10000000000 : ℝ)] ![(22611348211381/50000000000000 : ℝ), (11430460789883/100000000000000 : ℝ), (2709177673573/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352917197/10000000000 : ℝ)|^4819 ≤ (22611348211381/50000000000000 : ℝ)^3795
        have hw : |(5352917197/10000000000 : ℝ)|=(5352917197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90612449/500000000 : ℝ)|^4819 ≤ (11430460789883/100000000000000 : ℝ)^3795
        have hw : |(-90612449/500000000 : ℝ)|=(90612449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177274393/10000000000 : ℝ)|^4819 ≤ (2709177673573/6250000000000 : ℝ)^3795
        have hw : |(5177274393/10000000000 : ℝ)|=(5177274393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s2_2 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352917213/10000000000 : ℝ)*x 0 + (5177274283/10000000000 : ℝ)*x 1 + (-1812249103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352917213/10000000000 : ℝ)^4819 ≤ (45222696594407/100000000000000 : ℝ)^3795 := by
    have hnat : (5352917213 : ℕ)^4819*100000000000000^3795 ≤ 45222696594407^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352917213 10000000000 45222696594407 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177274283/10000000000 : ℝ)^4819 ≤ (8669368321537/20000000000000 : ℝ)^3795 := by
    have hnat : (5177274283 : ℕ)^4819*20000000000000^3795 ≤ 8669368321537^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177274283 10000000000 8669368321537 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1812249103/10000000000 : ℝ)^4819 ≤ (11430461775019/100000000000000 : ℝ)^3795 := by
    have hnat : (1812249103 : ℕ)^4819*100000000000000^3795 ≤ 11430461775019^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812249103 10000000000 11430461775019 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352917213/10000000000 : ℝ), (5177274283/10000000000 : ℝ), (-1812249103/10000000000 : ℝ)] ![(45222696594407/100000000000000 : ℝ), (8669368321537/20000000000000 : ℝ), (11430461775019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352917213/10000000000 : ℝ)|^4819 ≤ (45222696594407/100000000000000 : ℝ)^3795
        have hw : |(5352917213/10000000000 : ℝ)|=(5352917213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177274283/10000000000 : ℝ)|^4819 ≤ (8669368321537/20000000000000 : ℝ)^3795
        have hw : |(5177274283/10000000000 : ℝ)|=(5177274283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1812249103/10000000000 : ℝ)|^4819 ≤ (11430461775019/100000000000000 : ℝ)^3795
        have hw : |(-1812249103/10000000000 : ℝ)|=(1812249103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s2_3 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4199602073/10000000000 : ℝ)*x 0 + (964000917/2500000000 : ℝ)*x 1 + (4565767443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199602073/10000000000 : ℝ)^4819 ≤ (132922612087/400000000000 : ℝ)^3795 := by
    have hnat : (4199602073 : ℕ)^4819*400000000000^3795 ≤ 132922612087^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199602073 10000000000 132922612087 400000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (964000917/2500000000 : ℝ)^4819 ≤ (5963420417493/20000000000000 : ℝ)^3795 := by
    have hnat : (964000917 : ℕ)^4819*20000000000000^3795 ≤ 5963420417493^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964000917 2500000000 5963420417493 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4565767443/10000000000 : ℝ)^4819 ≤ (36952244875883/100000000000000 : ℝ)^3795 := by
    have hnat : (4565767443 : ℕ)^4819*100000000000000^3795 ≤ 36952244875883^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565767443 10000000000 36952244875883 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199602073/10000000000 : ℝ), (964000917/2500000000 : ℝ), (4565767443/10000000000 : ℝ)] ![(132922612087/400000000000 : ℝ), (5963420417493/20000000000000 : ℝ), (36952244875883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199602073/10000000000 : ℝ)|^4819 ≤ (132922612087/400000000000 : ℝ)^3795
        have hw : |(4199602073/10000000000 : ℝ)|=(4199602073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(964000917/2500000000 : ℝ)|^4819 ≤ (5963420417493/20000000000000 : ℝ)^3795
        have hw : |(964000917/2500000000 : ℝ)|=(964000917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4565767443/10000000000 : ℝ)|^4819 ≤ (36952244875883/100000000000000 : ℝ)^3795
        have hw : |(4565767443/10000000000 : ℝ)|=(4565767443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s2_4 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1666205959/10000000000 : ℝ)*x 0 + (2589737213/5000000000 : ℝ)*x 1 + (545828243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1666205959/10000000000 : ℝ)^4819 ≤ (10273743734473/100000000000000 : ℝ)^3795 := by
    have hnat : (1666205959 : ℕ)^4819*100000000000000^3795 ≤ 10273743734473^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666205959 10000000000 10273743734473 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589737213/5000000000 : ℝ)^4819 ≤ (8674046827983/20000000000000 : ℝ)^3795 := by
    have hnat : (2589737213 : ℕ)^4819*20000000000000^3795 ≤ 8674046827983^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589737213 5000000000 8674046827983 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545828243/1000000000 : ℝ)^4819 ≤ (11589005527213/25000000000000 : ℝ)^3795 := by
    have hnat : (545828243 : ℕ)^4819*25000000000000^3795 ≤ 11589005527213^3795*1000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545828243 1000000000 11589005527213 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1666205959/10000000000 : ℝ), (2589737213/5000000000 : ℝ), (545828243/1000000000 : ℝ)] ![(10273743734473/100000000000000 : ℝ), (8674046827983/20000000000000 : ℝ), (11589005527213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1666205959/10000000000 : ℝ)|^4819 ≤ (10273743734473/100000000000000 : ℝ)^3795
        have hw : |(-1666205959/10000000000 : ℝ)|=(1666205959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589737213/5000000000 : ℝ)|^4819 ≤ (8674046827983/20000000000000 : ℝ)^3795
        have hw : |(2589737213/5000000000 : ℝ)|=(2589737213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545828243/1000000000 : ℝ)|^4819 ≤ (11589005527213/25000000000000 : ℝ)^3795
        have hw : |(545828243/1000000000 : ℝ)|=(545828243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s2_5 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055500123/2000000000 : ℝ)*x 0 + (-765620399/5000000000 : ℝ)*x 1 + (2729141303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055500123/2000000000 : ℝ)^4819 ≤ (44415184808131/100000000000000 : ℝ)^3795 := by
    have hnat : (1055500123 : ℕ)^4819*100000000000000^3795 ≤ 44415184808131^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055500123 2000000000 44415184808131 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765620399/5000000000 : ℝ)^4819 ≤ (922879116771/10000000000000 : ℝ)^3795 := by
    have hnat : (765620399 : ℕ)^4819*10000000000000^3795 ≤ 922879116771^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765620399 5000000000 922879116771 10000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729141303/5000000000 : ℝ)^4819 ≤ (46356024006903/100000000000000 : ℝ)^3795 := by
    have hnat : (2729141303 : ℕ)^4819*100000000000000^3795 ≤ 46356024006903^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729141303 5000000000 46356024006903 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055500123/2000000000 : ℝ), (-765620399/5000000000 : ℝ), (2729141303/5000000000 : ℝ)] ![(44415184808131/100000000000000 : ℝ), (922879116771/10000000000000 : ℝ), (46356024006903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055500123/2000000000 : ℝ)|^4819 ≤ (44415184808131/100000000000000 : ℝ)^3795
        have hw : |(1055500123/2000000000 : ℝ)|=(1055500123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-765620399/5000000000 : ℝ)|^4819 ≤ (922879116771/10000000000000 : ℝ)^3795
        have hw : |(-765620399/5000000000 : ℝ)|=(765620399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729141303/5000000000 : ℝ)|^4819 ≤ (46356024006903/100000000000000 : ℝ)^3795
        have hw : |(2729141303/5000000000 : ℝ)|=(2729141303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s2_6 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638750869/5000000000 : ℝ)*x 0 + (5458281203/10000000000 : ℝ)*x 1 + (-1531241207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638750869/5000000000 : ℝ)^4819 ≤ (22207598404713/50000000000000 : ℝ)^3795 := by
    have hnat : (2638750869 : ℕ)^4819*50000000000000^3795 ≤ 22207598404713^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638750869 5000000000 22207598404713 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458281203/10000000000 : ℝ)^4819 ≤ (23178004438207/50000000000000 : ℝ)^3795 := by
    have hnat : (5458281203 : ℕ)^4819*50000000000000^3795 ≤ 23178004438207^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458281203 10000000000 23178004438207 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1531241207/10000000000 : ℝ)^4819 ≤ (9228794297893/100000000000000 : ℝ)^3795 := by
    have hnat : (1531241207 : ℕ)^4819*100000000000000^3795 ≤ 9228794297893^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531241207 10000000000 9228794297893 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638750869/5000000000 : ℝ), (5458281203/10000000000 : ℝ), (-1531241207/10000000000 : ℝ)] ![(22207598404713/50000000000000 : ℝ), (23178004438207/50000000000000 : ℝ), (9228794297893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638750869/5000000000 : ℝ)|^4819 ≤ (22207598404713/50000000000000 : ℝ)^3795
        have hw : |(2638750869/5000000000 : ℝ)|=(2638750869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458281203/10000000000 : ℝ)|^4819 ≤ (23178004438207/50000000000000 : ℝ)^3795
        have hw : |(5458281203/10000000000 : ℝ)|=(5458281203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1531241207/10000000000 : ℝ)|^4819 ≤ (9228794297893/100000000000000 : ℝ)^3795
        have hw : |(-1531241207/10000000000 : ℝ)|=(1531241207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s2_7 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049948051/2500000000 : ℝ)*x 0 + (912051223/2000000000 : ℝ)*x 1 + (96539387/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049948051/2500000000 : ℝ)^4819 ≤ (33232563453229/100000000000000 : ℝ)^3795 := by
    have hnat : (1049948051 : ℕ)^4819*100000000000000^3795 ≤ 33232563453229^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049948051 2500000000 33232563453229 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912051223/2000000000 : ℝ)^4819 ≤ (36895613424627/100000000000000 : ℝ)^3795 := by
    have hnat : (912051223 : ℕ)^4819*100000000000000^3795 ≤ 36895613424627^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912051223 2000000000 36895613424627 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96539387/250000000 : ℝ)^4819 ≤ (3733977889013/12500000000000 : ℝ)^3795 := by
    have hnat : (96539387 : ℕ)^4819*12500000000000^3795 ≤ 3733977889013^3795*250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96539387 250000000 3733977889013 12500000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049948051/2500000000 : ℝ), (912051223/2000000000 : ℝ), (96539387/250000000 : ℝ)] ![(33232563453229/100000000000000 : ℝ), (36895613424627/100000000000000 : ℝ), (3733977889013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049948051/2500000000 : ℝ)|^4819 ≤ (33232563453229/100000000000000 : ℝ)^3795
        have hw : |(1049948051/2500000000 : ℝ)|=(1049948051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(912051223/2000000000 : ℝ)|^4819 ≤ (36895613424627/100000000000000 : ℝ)^3795
        have hw : |(912051223/2000000000 : ℝ)|=(912051223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96539387/250000000 : ℝ)|^4819 ≤ (3733977889013/12500000000000 : ℝ)^3795
        have hw : |(96539387/250000000 : ℝ)|=(96539387/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1625_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8799/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10423/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8217/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8799/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8799/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8799/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8799/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8799/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8799/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4693/50000 : ℝ) ^ (4815/1024 : ℝ) ≤ (1473842321276849/100000000000000000000 : ℝ) := by
    have hpowers : (4693/50000 : ℝ)^4815 ≤ (1473842321276849/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4693 : ℕ)^4815*100000000000000000000^1024 ≤ 1473842321276849^1024*50000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4693 50000 1473842321276849 100000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4693/50000 : ℝ)) (X := (1473842321276849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8799/50000 : ℝ) ^ (4815/1024 : ℝ) ≤ (28317603589985349/100000000000000000000 : ℝ) := by
    have hpowers : (8799/50000 : ℝ)^4815 ≤ (28317603589985349/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8799 : ℕ)^4815*100000000000000000000^1024 ≤ 28317603589985349^1024*50000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8799 50000 28317603589985349 100000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8799/50000 : ℝ)) (X := (28317603589985349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001473842321276849/50000000000000000000 : ℝ) ≤ (10000062687311499/10000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50001473842321276849/50000000000000000000 : ℝ)^1024 ≤ (10000062687311499/10000000000000000 : ℝ)^4815 := by
      have hnat : (50001473842321276849 : ℕ)^1024*10000000000000000^4815 ≤ 10000062687311499^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001473842321276849 50000000000000000000 10000062687311499 10000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062687311499/10000000000000000 : ℝ)) (X := (50001473842321276849/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014895722955631099/50000000000000000000 : ℝ) ≤ (40002533986583/40000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50014895722955631099/50000000000000000000 : ℝ)^1024 ≤ (40002533986583/40000000000000 : ℝ)^4815 := by
      have hnat : (50014895722955631099 : ℕ)^1024*40000000000000^4815 ≤ 40002533986583^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014895722955631099 50000000000000000000 40002533986583 40000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40002533986583/40000000000000 : ℝ)) (X := (50014895722955631099/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028317603589985349/50000000000000000000 : ℝ) ≤ (10001204305980001/10000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50028317603589985349/50000000000000000000 : ℝ)^1024 ≤ (10001204305980001/10000000000000000 : ℝ)^4815 := by
      have hnat : (50028317603589985349 : ℕ)^1024*10000000000000000^4815 ≤ 10001204305980001^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028317603589985349 50000000000000000000 10001204305980001 10000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001204305980001/10000000000000000 : ℝ)) (X := (50028317603589985349/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1473842321276849/100000000000000000000 : ℝ) ≤ ((1282965618052804219/1283125000000000000 : ℝ)+2*(570809334251/821200000000000 : ℝ)*(4693/50000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (1282965618052804219/1283125000000000000 : ℝ)+2*(570809334251/821200000000000 : ℝ)*(4693/50000 : ℝ)=(10000062687311499/10000000000000000 : ℝ) by norm_num, show 1+2*(1473842321276849/100000000000000000000 : ℝ)=(50001473842321276849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28317603589985349/100000000000000000000 : ℝ)+(1473842321276849/100000000000000000000 : ℝ) ≤ ((1282965618052804219/1283125000000000000 : ℝ)+(570809334251/821200000000000 : ℝ)*((8799/50000 : ℝ)+(4693/50000 : ℝ)))^(4815/1024 : ℝ) := by
    rw [show (1282965618052804219/1283125000000000000 : ℝ)+(570809334251/821200000000000 : ℝ)*((8799/50000 : ℝ)+(4693/50000 : ℝ))=(40002533986583/40000000000000 : ℝ) by norm_num, show 1+(28317603589985349/100000000000000000000 : ℝ)+(1473842321276849/100000000000000000000 : ℝ)=(50014895722955631099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28317603589985349/100000000000000000000 : ℝ) ≤ ((1282965618052804219/1283125000000000000 : ℝ)+2*(570809334251/821200000000000 : ℝ)*(8799/50000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (1282965618052804219/1283125000000000000 : ℝ)+2*(570809334251/821200000000000 : ℝ)*(8799/50000 : ℝ)=(10001204305980001/10000000000000000 : ℝ) by norm_num, show 1+2*(28317603589985349/100000000000000000000 : ℝ)=(50028317603589985349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1282965618052804219/1283125000000000000 : ℝ)*(X 1 0+X 2 0)+(570809334251/821200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (4693/50000 : ℝ)) (hi := (8799/50000 : ℝ)) (c := (1282965618052804219/1283125000000000000 : ℝ)) (alpha := (570809334251/821200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1282965618052804219/1283125000000000000 : ℝ)*(X 0 1+X 2 1)+(570809334251/821200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (4693/50000 : ℝ)) (hi := (8799/50000 : ℝ)) (c := (1282965618052804219/1283125000000000000 : ℝ)) (alpha := (570809334251/821200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1282965618052804219/1283125000000000000 : ℝ)*(X 0 2+X 1 2)+(570809334251/821200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (4693/50000 : ℝ)) (hi := (8799/50000 : ℝ)) (c := (1282965618052804219/1283125000000000000 : ℝ)) (alpha := (570809334251/821200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416532597/2500000000 : ℝ)*X 0 0+(1365126563/2500000000 : ℝ)*X 0 1+(5177274317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352917197/10000000000 : ℝ)*X 1 0+(-90612449/500000000 : ℝ)*X 1 1+(5177274393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352917213/10000000000 : ℝ)*X 2 0+(5177274283/10000000000 : ℝ)*X 2 1+(-1812249103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199602073/10000000000 : ℝ)*X 0 0+(964000917/2500000000 : ℝ)*X 0 1+(4565767443/10000000000 : ℝ)*X 0 2+(4199602073/10000000000 : ℝ)*X 1 0+(964000917/2500000000 : ℝ)*X 1 1+(4565767443/10000000000 : ℝ)*X 1 2+(4199602073/10000000000 : ℝ)*X 2 0+(964000917/2500000000 : ℝ)*X 2 1+(4565767443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1666205959/10000000000 : ℝ)*X 0 0+(2589737213/5000000000 : ℝ)*X 0 1+(545828243/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055500123/2000000000 : ℝ)*X 1 0+(-765620399/5000000000 : ℝ)*X 1 1+(2729141303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638750869/5000000000 : ℝ)*X 2 0+(5458281203/10000000000 : ℝ)*X 2 1+(-1531241207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1049948051/2500000000 : ℝ)*X 0 0+(912051223/2000000000 : ℝ)*X 0 1+(96539387/250000000 : ℝ)*X 0 2+(1049948051/2500000000 : ℝ)*X 1 0+(912051223/2000000000 : ℝ)*X 1 1+(96539387/250000000 : ℝ)*X 1 2+(1049948051/2500000000 : ℝ)*X 2 0+(912051223/2000000000 : ℝ)*X 2 1+(96539387/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236536032968237974106631/20530000000000000000000000000 : ℝ) := by norm_num
    linear_combination (909390243/50000000000000 : ℝ)*(base19) + (344500451/20000000000000 : ℝ)*(base23) + (57186087/100000000000000 : ℝ)*(lower2) + (6546629/2000000000000 : ℝ)*(upper3) + (31297559/20000000000000 : ℝ)*(upper5) + (1234914065909877/50000000000000 : ℝ)*(major0) + (1234914065909877/50000000000000 : ℝ)*(major1) + (1234914065909877/50000000000000 : ℝ)*(major2) + (1765349265939271/50000000000000 : ℝ)*(sp0) + (706143446771129/20000000000000 : ℝ)*(sp1) + (882679332533469/25000000000000 : ℝ)*(sp2) + (281785459640949/20000000000000 : ℝ)*(sp3) + (5130189397/25000000000000 : ℝ)*(sp4) + (1905749843/20000000000000 : ℝ)*(sp7) + (35223420673849/2500000000000 : ℝ)*(f.failure) + (353071905263613/10000000000000 : ℝ)*(f.sum) + (11979858023083/20530000000000000000000000000 : ℝ)*base66 + (197030361760951501/128312500000000000000000000000000 : ℝ)*base67 + (698032108329951501/128312500000000000000000000000000 : ℝ)*base69 + (342140269997889001/128312500000000000000000000000000 : ℝ)*base71 + (155372817913923/20530000000000000000000000000 : ℝ)*base74 + (506490428860235999/128312500000000000000000000000000 : ℝ)*base76 + (389084505859548499/128312500000000000000000000000000 : ℝ)*base78 + (839070215070798499/128312500000000000000000000000000 : ℝ)*base80 + (35356225593417/20530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (632303/125000000000000000000 : ℝ)*base89 + (632303/125000000000000000000 : ℝ)*base91 + (632303/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195869317145619324611439591/16039062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1462418061/100000000000000 : ℝ)*(base19) + (2621556769/100000000000000 : ℝ)*(base23) + (316539747/100000000000000 : ℝ)*(upper3) + (84413393/50000000000000 : ℝ)*(lower4) + (1254490898082451/50000000000000 : ℝ)*(major0) + (1254490898082451/50000000000000 : ℝ)*(major1) + (1254490898082451/50000000000000 : ℝ)*(major2) + (2923579791/20000000000000 : ℝ)*(sp1) + (19938461607/100000000000000 : ℝ)*(sp2) + (237644223/100000000000000 : ℝ)*(sp3) + (717338156003313/20000000000000 : ℝ)*(sp4) + (896668674924887/25000000000000 : ℝ)*(sp5) + (3586668219998189/100000000000000 : ℝ)*(sp6) + (357818041900437/25000000000000 : ℝ)*(sp7) + (357818101311493/25000000000000 : ℝ)*(f.failure) + (717338156003313/20000000000000 : ℝ)*(f.sum) + (35503145510121/20530000000000000000000000000 : ℝ)*base65 + (154448971328949663/128312500000000000000000000000000 : ℝ)*base67 + (459970059268862837/128312500000000000000000000000000 : ℝ)*base70 + (360794023587050337/128312500000000000000000000000000 : ℝ)*base72 + (53274165125801/20530000000000000000000000000 : ℝ)*base73 + (1643204176105574663/128312500000000000000000000000000 : ℝ)*base75 + (430242217009175337/128312500000000000000000000000000 : ℝ)*base78 + (351465076875675337/128312500000000000000000000000000 : ℝ)*base80 + (25817663291151/20530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (11999971/1250000000000000000000 : ℝ)*base89 + (11999971/1250000000000000000000 : ℝ)*base91 + (11999971/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1625_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8799/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8217/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1625_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1625_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8217/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1625_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1625_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1625_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8217/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1625_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
