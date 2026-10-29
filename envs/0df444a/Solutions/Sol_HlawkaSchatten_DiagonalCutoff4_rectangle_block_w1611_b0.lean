-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1611_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:42.287909+00:00
-- url     : https://prove2.me/submissions/469b6ddf-a6e9-421c-b723-4ddd2161c9de

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
theorem support_rectangle_w1611_s0_0 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156363011/1000000000 : ℝ)*x 0 + (5835768781/10000000000 : ℝ)*x 1 + (4893759523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156363011/1000000000 : ℝ)^4763 ≤ (4703287202969/50000000000000 : ℝ)^3739 := by
    have hnat : (156363011 : ℕ)^4763*50000000000000^3739 ≤ 4703287202969^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156363011 1000000000 4703287202969 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5835768781/10000000000 : ℝ)^4763 ≤ (10070924678443/20000000000000 : ℝ)^3739 := by
    have hnat : (5835768781 : ℕ)^4763*20000000000000^3739 ≤ 10070924678443^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835768781 10000000000 10070924678443 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4893759523/10000000000 : ℝ)^4763 ≤ (10059700545641/25000000000000 : ℝ)^3739 := by
    have hnat : (4893759523 : ℕ)^4763*25000000000000^3739 ≤ 10059700545641^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893759523 10000000000 10059700545641 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156363011/1000000000 : ℝ), (5835768781/10000000000 : ℝ), (4893759523/10000000000 : ℝ)] ![(4703287202969/50000000000000 : ℝ), (10070924678443/20000000000000 : ℝ), (10059700545641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156363011/1000000000 : ℝ)|^4763 ≤ (4703287202969/50000000000000 : ℝ)^3739
        have hw : |(-156363011/1000000000 : ℝ)|=(156363011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5835768781/10000000000 : ℝ)|^4763 ≤ (10070924678443/20000000000000 : ℝ)^3739
        have hw : |(5835768781/10000000000 : ℝ)|=(5835768781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4893759523/10000000000 : ℝ)|^4763 ≤ (10059700545641/25000000000000 : ℝ)^3739
        have hw : |(4893759523/10000000000 : ℝ)|=(4893759523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s0_1 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2726652869/5000000000 : ℝ)*x 0 + (-1042536873/5000000000 : ℝ)*x 1 + (4893759283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2726652869/5000000000 : ℝ)^4763 ≤ (9237806690201/20000000000000 : ℝ)^3739 := by
    have hnat : (2726652869 : ℕ)^4763*20000000000000^3739 ≤ 9237806690201^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726652869 5000000000 9237806690201 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042536873/5000000000 : ℝ)^4763 ≤ (3393041716007/25000000000000 : ℝ)^3739 := by
    have hnat : (1042536873 : ℕ)^4763*25000000000000^3739 ≤ 3393041716007^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042536873 5000000000 3393041716007 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4893759283/10000000000 : ℝ)^4763 ≤ (20119399834359/50000000000000 : ℝ)^3739 := by
    have hnat : (4893759283 : ℕ)^4763*50000000000000^3739 ≤ 20119399834359^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893759283 10000000000 20119399834359 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2726652869/5000000000 : ℝ), (-1042536873/5000000000 : ℝ), (4893759283/10000000000 : ℝ)] ![(9237806690201/20000000000000 : ℝ), (3393041716007/25000000000000 : ℝ), (20119399834359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2726652869/5000000000 : ℝ)|^4763 ≤ (9237806690201/20000000000000 : ℝ)^3739
        have hw : |(2726652869/5000000000 : ℝ)|=(2726652869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042536873/5000000000 : ℝ)|^4763 ≤ (3393041716007/25000000000000 : ℝ)^3739
        have hw : |(-1042536873/5000000000 : ℝ)|=(1042536873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4893759283/10000000000 : ℝ)|^4763 ≤ (20119399834359/50000000000000 : ℝ)^3739
        have hw : |(4893759283/10000000000 : ℝ)|=(4893759283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s0_2 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (681663193/1250000000 : ℝ)*x 0 + (4893759361/10000000000 : ℝ)*x 1 + (-2085073899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681663193/1250000000 : ℝ)^4763 ≤ (46189031357829/100000000000000 : ℝ)^3739 := by
    have hnat : (681663193 : ℕ)^4763*100000000000000^3739 ≤ 46189031357829^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681663193 1250000000 46189031357829 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4893759361/10000000000 : ℝ)^4763 ≤ (20119400242859/50000000000000 : ℝ)^3739 := by
    have hnat : (4893759361 : ℕ)^4763*50000000000000^3739 ≤ 20119400242859^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893759361 10000000000 20119400242859 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085073899/10000000000 : ℝ)^4763 ≤ (6786084066343/50000000000000 : ℝ)^3739 := by
    have hnat : (2085073899 : ℕ)^4763*50000000000000^3739 ≤ 6786084066343^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085073899 10000000000 6786084066343 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(681663193/1250000000 : ℝ), (4893759361/10000000000 : ℝ), (-2085073899/10000000000 : ℝ)] ![(46189031357829/100000000000000 : ℝ), (20119400242859/50000000000000 : ℝ), (6786084066343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(681663193/1250000000 : ℝ)|^4763 ≤ (46189031357829/100000000000000 : ℝ)^3739
        have hw : |(681663193/1250000000 : ℝ)|=(681663193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4893759361/10000000000 : ℝ)|^4763 ≤ (20119400242859/50000000000000 : ℝ)^3739
        have hw : |(4893759361/10000000000 : ℝ)|=(4893759361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085073899/10000000000 : ℝ)|^4763 ≤ (6786084066343/50000000000000 : ℝ)^3739
        have hw : |(-2085073899/10000000000 : ℝ)|=(2085073899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s0_3 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2054644691/5000000000 : ℝ)*x 0 + (1537227313/5000000000 : ℝ)*x 1 + (539234301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054644691/5000000000 : ℝ)^4763 ≤ (4026234120713/12500000000000 : ℝ)^3739 := by
    have hnat : (2054644691 : ℕ)^4763*12500000000000^3739 ≤ 4026234120713^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054644691 5000000000 4026234120713 12500000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537227313/5000000000 : ℝ)^4763 ≤ (22257845556787/100000000000000 : ℝ)^3739 := by
    have hnat : (1537227313 : ℕ)^4763*100000000000000^3739 ≤ 22257845556787^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537227313 5000000000 22257845556787 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539234301/1000000000 : ℝ)^4763 ≤ (2845767591263/6250000000000 : ℝ)^3739 := by
    have hnat : (539234301 : ℕ)^4763*6250000000000^3739 ≤ 2845767591263^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539234301 1000000000 2845767591263 6250000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2054644691/5000000000 : ℝ), (1537227313/5000000000 : ℝ), (539234301/1000000000 : ℝ)] ![(4026234120713/12500000000000 : ℝ), (22257845556787/100000000000000 : ℝ), (2845767591263/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2054644691/5000000000 : ℝ)|^4763 ≤ (4026234120713/12500000000000 : ℝ)^3739
        have hw : |(2054644691/5000000000 : ℝ)|=(2054644691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1537227313/5000000000 : ℝ)|^4763 ≤ (22257845556787/100000000000000 : ℝ)^3739
        have hw : |(1537227313/5000000000 : ℝ)|=(1537227313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539234301/1000000000 : ℝ)|^4763 ≤ (2845767591263/6250000000000 : ℝ)^3739
        have hw : |(539234301/1000000000 : ℝ)|=(539234301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s0_4 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1566409613/10000000000 : ℝ)*x 0 + (122939811/250000000 : ℝ)*x 1 + (5811089903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1566409613/10000000000 : ℝ)^4763 ≤ (9427880085421/100000000000000 : ℝ)^3739 := by
    have hnat : (1566409613 : ℕ)^4763*100000000000000^3739 ≤ 9427880085421^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566409613 10000000000 9427880085421 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122939811/250000000 : ℝ)^4763 ≤ (10122150759733/25000000000000 : ℝ)^3739 := by
    have hnat : (122939811 : ℕ)^4763*25000000000000^3739 ≤ 10122150759733^3739*250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122939811 250000000 10122150759733 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5811089903/10000000000 : ℝ)^4763 ≤ (50083516861681/100000000000000 : ℝ)^3739 := by
    have hnat : (5811089903 : ℕ)^4763*100000000000000^3739 ≤ 50083516861681^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5811089903 10000000000 50083516861681 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1566409613/10000000000 : ℝ), (122939811/250000000 : ℝ), (5811089903/10000000000 : ℝ)] ![(9427880085421/100000000000000 : ℝ), (10122150759733/25000000000000 : ℝ), (50083516861681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1566409613/10000000000 : ℝ)|^4763 ≤ (9427880085421/100000000000000 : ℝ)^3739
        have hw : |(-1566409613/10000000000 : ℝ)|=(1566409613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122939811/250000000 : ℝ)|^4763 ≤ (10122150759733/25000000000000 : ℝ)^3739
        have hw : |(122939811/250000000 : ℝ)|=(122939811/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5811089903/10000000000 : ℝ)|^4763 ≤ (50083516861681/100000000000000 : ℝ)^3739
        have hw : |(5811089903/10000000000 : ℝ)|=(5811089903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s0_5 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196032589/10000000000 : ℝ)*x 0 + (-1167742673/10000000000 : ℝ)*x 1 + (726386267/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196032589/10000000000 : ℝ)^4763 ≤ (43431308595247/100000000000000 : ℝ)^3739 := by
    have hnat : (5196032589 : ℕ)^4763*100000000000000^3739 ≤ 43431308595247^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196032589 10000000000 43431308595247 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167742673/10000000000 : ℝ)^4763 ≤ (1621292995593/25000000000000 : ℝ)^3739 := by
    have hnat : (1167742673 : ℕ)^4763*25000000000000^3739 ≤ 1621292995593^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167742673 10000000000 1621292995593 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (726386267/1250000000 : ℝ)^4763 ≤ (25041759709893/50000000000000 : ℝ)^3739 := by
    have hnat : (726386267 : ℕ)^4763*50000000000000^3739 ≤ 25041759709893^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726386267 1250000000 25041759709893 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196032589/10000000000 : ℝ), (-1167742673/10000000000 : ℝ), (726386267/1250000000 : ℝ)] ![(43431308595247/100000000000000 : ℝ), (1621292995593/25000000000000 : ℝ), (25041759709893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196032589/10000000000 : ℝ)|^4763 ≤ (43431308595247/100000000000000 : ℝ)^3739
        have hw : |(5196032589/10000000000 : ℝ)|=(5196032589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1167742673/10000000000 : ℝ)|^4763 ≤ (1621292995593/25000000000000 : ℝ)^3739
        have hw : |(-1167742673/10000000000 : ℝ)|=(1167742673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(726386267/1250000000 : ℝ)|^4763 ≤ (25041759709893/50000000000000 : ℝ)^3739
        have hw : |(726386267/1250000000 : ℝ)|=(726386267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s0_6 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598016371/5000000000 : ℝ)*x 0 + (1162217953/2000000000 : ℝ)*x 1 + (-145967877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598016371/5000000000 : ℝ)^4763 ≤ (43431310224347/100000000000000 : ℝ)^3739 := by
    have hnat : (2598016371 : ℕ)^4763*100000000000000^3739 ≤ 43431310224347^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598016371 5000000000 43431310224347 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162217953/2000000000 : ℝ)^4763 ≤ (50083515346581/100000000000000 : ℝ)^3739 := by
    have hnat : (1162217953 : ℕ)^4763*100000000000000^3739 ≤ 50083515346581^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162217953 2000000000 50083515346581 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145967877/1250000000 : ℝ)^4763 ≤ (6485174408947/100000000000000 : ℝ)^3739 := by
    have hnat : (145967877 : ℕ)^4763*100000000000000^3739 ≤ 6485174408947^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145967877 1250000000 6485174408947 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598016371/5000000000 : ℝ), (1162217953/2000000000 : ℝ), (-145967877/1250000000 : ℝ)] ![(43431310224347/100000000000000 : ℝ), (50083515346581/100000000000000 : ℝ), (6485174408947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598016371/5000000000 : ℝ)|^4763 ≤ (43431310224347/100000000000000 : ℝ)^3739
        have hw : |(2598016371/5000000000 : ℝ)|=(2598016371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162217953/2000000000 : ℝ)|^4763 ≤ (50083515346581/100000000000000 : ℝ)^3739
        have hw : |(1162217953/2000000000 : ℝ)|=(1162217953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145967877/1250000000 : ℝ)|^4763 ≤ (6485174408947/100000000000000 : ℝ)^3739
        have hw : |(-145967877/1250000000 : ℝ)|=(145967877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s0_7 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4116130391/10000000000 : ℝ)*x 0 + (2666849763/5000000000 : ℝ)*x 1 + (3135179113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116130391/10000000000 : ℝ)^4763 ≤ (16139097950549/50000000000000 : ℝ)^3739 := by
    have hnat : (4116130391 : ℕ)^4763*50000000000000^3739 ≤ 16139097950549^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116130391 10000000000 16139097950549 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2666849763/5000000000 : ℝ)^4763 ≤ (44902430450647/100000000000000 : ℝ)^3739 := by
    have hnat : (2666849763 : ℕ)^4763*100000000000000^3739 ≤ 44902430450647^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666849763 5000000000 44902430450647 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3135179113/10000000000 : ℝ)^4763 ≤ (22819373640183/100000000000000 : ℝ)^3739 := by
    have hnat : (3135179113 : ℕ)^4763*100000000000000^3739 ≤ 22819373640183^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3135179113 10000000000 22819373640183 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116130391/10000000000 : ℝ), (2666849763/5000000000 : ℝ), (3135179113/10000000000 : ℝ)] ![(16139097950549/50000000000000 : ℝ), (44902430450647/100000000000000 : ℝ), (22819373640183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116130391/10000000000 : ℝ)|^4763 ≤ (16139097950549/50000000000000 : ℝ)^3739
        have hw : |(4116130391/10000000000 : ℝ)|=(4116130391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2666849763/5000000000 : ℝ)|^4763 ≤ (44902430450647/100000000000000 : ℝ)^3739
        have hw : |(2666849763/5000000000 : ℝ)|=(2666849763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3135179113/10000000000 : ℝ)|^4763 ≤ (22819373640183/100000000000000 : ℝ)^3739
        have hw : |(3135179113/10000000000 : ℝ)|=(3135179113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1611_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1011/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24219/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4759/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4759 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4759*1^1024 ≤ 0^1024*1^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4759/1024 : ℝ) ≤ (88403482083442979/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4759 ≤ (88403482083442979/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4759*6250000000000000000^1024 ≤ 88403482083442979^1024*5^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 88403482083442979 6250000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (88403482083442979/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4759 := by
      have hnat : (1 : ℕ)^1024*1^4759 ≤ 1^4759*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6338403482083442979/6250000000000000000 : ℝ) ≤ (5015133749166919/5000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (6338403482083442979/6250000000000000000 : ℝ)^1024 ≤ (5015133749166919/5000000000000000 : ℝ)^4759 := by
      have hnat : (6338403482083442979 : ℕ)^1024*5000000000000000^4759 ≤ 5015133749166919^4759*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6338403482083442979 6250000000000000000 5015133749166919 5000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015133749166919/5000000000000000 : ℝ)) (X := (6338403482083442979/6250000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3213403482083442979/3125000000000000000 : ℝ) ≤ (2515133749166919/2500000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (3213403482083442979/3125000000000000000 : ℝ)^1024 ≤ (2515133749166919/2500000000000000 : ℝ)^4759 := by
      have hnat : (3213403482083442979 : ℕ)^1024*2500000000000000^4759 ≤ 2515133749166919^4759*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3213403482083442979 3125000000000000000 2515133749166919 2500000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515133749166919/2500000000000000 : ℝ)) (X := (3213403482083442979/3125000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15133749166919/2000000000000000 : ℝ)*(0 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15133749166919/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(88403482083442979/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15133749166919/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4759/1024 : ℝ) := by
    rw [show (1 : ℝ)+(15133749166919/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5015133749166919/5000000000000000 : ℝ) by norm_num, show 1+(88403482083442979/6250000000000000000 : ℝ)+(0 : ℝ)=(6338403482083442979/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(88403482083442979/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15133749166919/2000000000000000 : ℝ)*(2/5 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15133749166919/2000000000000000 : ℝ)*(2/5 : ℝ)=(2515133749166919/2500000000000000 : ℝ) by norm_num, show 1+2*(88403482083442979/6250000000000000000 : ℝ)=(3213403482083442979/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15133749166919/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15133749166919/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15133749166919/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15133749166919/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15133749166919/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15133749166919/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-156363011/1000000000 : ℝ)*X 0 0+(5835768781/10000000000 : ℝ)*X 0 1+(4893759523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2726652869/5000000000 : ℝ)*X 1 0+(-1042536873/5000000000 : ℝ)*X 1 1+(4893759283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((681663193/1250000000 : ℝ)*X 2 0+(4893759361/10000000000 : ℝ)*X 2 1+(-2085073899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2054644691/5000000000 : ℝ)*X 0 0+(1537227313/5000000000 : ℝ)*X 0 1+(539234301/1000000000 : ℝ)*X 0 2+(2054644691/5000000000 : ℝ)*X 1 0+(1537227313/5000000000 : ℝ)*X 1 1+(539234301/1000000000 : ℝ)*X 1 2+(2054644691/5000000000 : ℝ)*X 2 0+(1537227313/5000000000 : ℝ)*X 2 1+(539234301/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1566409613/10000000000 : ℝ)*X 0 0+(122939811/250000000 : ℝ)*X 0 1+(5811089903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5196032589/10000000000 : ℝ)*X 1 0+(-1167742673/10000000000 : ℝ)*X 1 1+(726386267/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2598016371/5000000000 : ℝ)*X 2 0+(1162217953/2000000000 : ℝ)*X 2 1+(-145967877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4116130391/10000000000 : ℝ)*X 0 0+(2666849763/5000000000 : ℝ)*X 0 1+(3135179113/10000000000 : ℝ)*X 0 2+(4116130391/10000000000 : ℝ)*X 1 0+(2666849763/5000000000 : ℝ)*X 1 1+(3135179113/10000000000 : ℝ)*X 1 2+(4116130391/10000000000 : ℝ)*X 2 0+(2666849763/5000000000 : ℝ)*X 2 1+(3135179113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (348974844097264548266433/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17359861/100000000000000 : ℝ)*(base1) + (266391899/20000000000000 : ℝ)*(base19) + (1294194433/100000000000000 : ℝ)*(base23) + (51666291/25000000000000 : ℝ)*(upper3) + (9258259/6250000000000 : ℝ)*(upper5) + (373250589219331/50000000000000 : ℝ)*(major0) + (373250589219331/50000000000000 : ℝ)*(major1) + (373250589219331/50000000000000 : ℝ)*(major2) + (265391435259669/25000000000000 : ℝ)*(sp0) + (530784591355521/50000000000000 : ℝ)*(sp1) + (132696152559513/12500000000000 : ℝ)*(sp2) + (431429240724479/100000000000000 : ℝ)*(sp3) + (2395495861/50000000000000 : ℝ)*(sp4) + (73483517/3125000000000 : ℝ)*(sp7) + (431431609556883/100000000000000 : ℝ)*(f.failure) + (1061570514670537/100000000000000 : ℝ)*(f.sum) + (81888383711189/50000000000000000000000000000 : ℝ)*base65 + (674792142888811/100000000000000000000000000000 : ℝ)*base68 + (669362842911189/100000000000000000000000000000 : ℝ)*base69 + (47318747288811/100000000000000000000000000000 : ℝ)*base72 + (154061212788811/50000000000000000000000000000 : ℝ)*base74 + (545662005711189/100000000000000000000000000000 : ℝ)*base75 + (100134905288811/100000000000000000000000000000 : ℝ)*base78 + (454942466311189/100000000000000000000000000000 : ℝ)*base79 + (295918532211189/50000000000000000000000000000 : ℝ)*base81 + (8448019/1250000000000000000000 : ℝ)*base90 + (8448019/1250000000000000000000 : ℝ)*base92 + (8448019/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1117495692971907417/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (55165297/5000000000000 : ℝ)*(base19) + (114654791/10000000000000 : ℝ)*(base23) + (4083303/2000000000000 : ℝ)*(base32) + (211583491/100000000000000 : ℝ)*(upper3) + (53476883/100000000000000 : ℝ)*(upper5) + (196755920806953/25000000000000 : ℝ)*(major0) + (196755920806953/25000000000000 : ℝ)*(major1) + (196755920806953/25000000000000 : ℝ)*(major2) + (753977397/25000000000000 : ℝ)*(sp1) + (3223669251/100000000000000 : ℝ)*(sp2) + (559598031898063/50000000000000 : ℝ)*(sp4) + (559595972290299/50000000000000 : ℝ)*(sp5) + (223838338715793/20000000000000 : ℝ)*(sp6) + (227425456122529/50000000000000 : ℝ)*(sp7) + (14214097387819/3125000000000 : ℝ)*(f.failure) + (559598031898063/50000000000000 : ℝ)*(f.sum) + (167988212193/25000000000000000000000000000 : ℝ)*base66 + (287235475387807/50000000000000000000000000000 : ℝ)*base67 + (34292506187807/50000000000000000000000000000 : ℝ)*base69 + (208297880587807/50000000000000000000000000000 : ℝ)*base71 + (40035712362193/25000000000000000000000000000 : ℝ)*base74 + (383823958487807/50000000000000000000000000000 : ℝ)*base75 + (151879110187807/50000000000000000000000000000 : ℝ)*base77 + (454184755587807/50000000000000000000000000000 : ℝ)*base79 + (121468913837193/25000000000000000000000000000 : ℝ)*base82 + (324367/39062500000000000000 : ℝ)*base90 + (324367/39062500000000000000 : ℝ)*base92 + (324367/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1611_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1011/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24219/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1611_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1611_s1_0 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1686575009/10000000000 : ℝ)*x 0 + (5528964347/10000000000 : ℝ)*x 1 + (1024207881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686575009/10000000000 : ℝ)^4763 ≤ (2071742056591/20000000000000 : ℝ)^3739 := by
    have hnat : (1686575009 : ℕ)^4763*20000000000000^3739 ≤ 2071742056591^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686575009 10000000000 2071742056591 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528964347/10000000000 : ℝ)^4763 ≤ (11751725753743/25000000000000 : ℝ)^3739 := by
    have hnat : (5528964347 : ℕ)^4763*25000000000000^3739 ≤ 11751725753743^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528964347 10000000000 11751725753743 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024207881/2000000000 : ℝ)^4763 ≤ (21317193343299/50000000000000 : ℝ)^3739 := by
    have hnat : (1024207881 : ℕ)^4763*50000000000000^3739 ≤ 21317193343299^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024207881 2000000000 21317193343299 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1686575009/10000000000 : ℝ), (5528964347/10000000000 : ℝ), (1024207881/2000000000 : ℝ)] ![(2071742056591/20000000000000 : ℝ), (11751725753743/25000000000000 : ℝ), (21317193343299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1686575009/10000000000 : ℝ)|^4763 ≤ (2071742056591/20000000000000 : ℝ)^3739
        have hw : |(-1686575009/10000000000 : ℝ)|=(1686575009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528964347/10000000000 : ℝ)|^4763 ≤ (11751725753743/25000000000000 : ℝ)^3739
        have hw : |(5528964347/10000000000 : ℝ)|=(5528964347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024207881/2000000000 : ℝ)|^4763 ≤ (21317193343299/50000000000000 : ℝ)^3739
        have hw : |(1024207881/2000000000 : ℝ)|=(1024207881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s1_1 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074332943/2000000000 : ℝ)*x 0 + (-1899877931/10000000000 : ℝ)*x 1 + (1024207851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074332943/2000000000 : ℝ)^4763 ≤ (22654987158017/50000000000000 : ℝ)^3739 := by
    have hnat : (1074332943 : ℕ)^4763*50000000000000^3739 ≤ 22654987158017^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074332943 2000000000 22654987158017 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1899877931/10000000000 : ℝ)^4763 ≤ (3013910143099/25000000000000 : ℝ)^3739 := by
    have hnat : (1899877931 : ℕ)^4763*25000000000000^3739 ≤ 3013910143099^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899877931 10000000000 3013910143099 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024207851/2000000000 : ℝ)^4763 ≤ (10658596273947/25000000000000 : ℝ)^3739 := by
    have hnat : (1024207851 : ℕ)^4763*25000000000000^3739 ≤ 10658596273947^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024207851 2000000000 10658596273947 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074332943/2000000000 : ℝ), (-1899877931/10000000000 : ℝ), (1024207851/2000000000 : ℝ)] ![(22654987158017/50000000000000 : ℝ), (3013910143099/25000000000000 : ℝ), (10658596273947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074332943/2000000000 : ℝ)|^4763 ≤ (22654987158017/50000000000000 : ℝ)^3739
        have hw : |(1074332943/2000000000 : ℝ)|=(1074332943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1899877931/10000000000 : ℝ)|^4763 ≤ (3013910143099/25000000000000 : ℝ)^3739
        have hw : |(-1899877931/10000000000 : ℝ)|=(1899877931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024207851/2000000000 : ℝ)|^4763 ≤ (10658596273947/25000000000000 : ℝ)^3739
        have hw : |(1024207851/2000000000 : ℝ)|=(1024207851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s1_2 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671458061/1250000000 : ℝ)*x 0 + (640129927/1250000000 : ℝ)*x 1 + (-949939011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671458061/1250000000 : ℝ)^4763 ≤ (22654985938449/50000000000000 : ℝ)^3739 := by
    have hnat : (671458061 : ℕ)^4763*50000000000000^3739 ≤ 22654985938449^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671458061 1250000000 22654985938449 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640129927/1250000000 : ℝ)^4763 ≤ (42634386803257/100000000000000 : ℝ)^3739 := by
    have hnat : (640129927 : ℕ)^4763*100000000000000^3739 ≤ 42634386803257^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640129927 1250000000 42634386803257 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949939011/5000000000 : ℝ)^4763 ≤ (6027820653989/50000000000000 : ℝ)^3739 := by
    have hnat : (949939011 : ℕ)^4763*50000000000000^3739 ≤ 6027820653989^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949939011 5000000000 6027820653989 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671458061/1250000000 : ℝ), (640129927/1250000000 : ℝ), (-949939011/5000000000 : ℝ)] ![(22654985938449/50000000000000 : ℝ), (42634386803257/100000000000000 : ℝ), (6027820653989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671458061/1250000000 : ℝ)|^4763 ≤ (22654985938449/50000000000000 : ℝ)^3739
        have hw : |(671458061/1250000000 : ℝ)|=(671458061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640129927/1250000000 : ℝ)|^4763 ≤ (42634386803257/100000000000000 : ℝ)^3739
        have hw : |(640129927/1250000000 : ℝ)|=(640129927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949939011/5000000000 : ℝ)|^4763 ≤ (6027820653989/50000000000000 : ℝ)^3739
        have hw : |(-949939011/5000000000 : ℝ)|=(949939011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s1_3 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4200608859/10000000000 : ℝ)*x 0 + (744345213/2000000000 : ℝ)*x 1 + (118136433/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200608859/10000000000 : ℝ)^4763 ≤ (33124456498129/100000000000000 : ℝ)^3739 := by
    have hnat : (4200608859 : ℕ)^4763*100000000000000^3739 ≤ 33124456498129^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200608859 10000000000 33124456498129 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744345213/2000000000 : ℝ)^4763 ≤ (14195613625687/50000000000000 : ℝ)^3739 := by
    have hnat : (744345213 : ℕ)^4763*50000000000000^3739 ≤ 14195613625687^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744345213 2000000000 14195613625687 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118136433/250000000 : ℝ)^4763 ≤ (38484316238881/100000000000000 : ℝ)^3739 := by
    have hnat : (118136433 : ℕ)^4763*100000000000000^3739 ≤ 38484316238881^3739*250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118136433 250000000 38484316238881 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200608859/10000000000 : ℝ), (744345213/2000000000 : ℝ), (118136433/250000000 : ℝ)] ![(33124456498129/100000000000000 : ℝ), (14195613625687/50000000000000 : ℝ), (38484316238881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200608859/10000000000 : ℝ)|^4763 ≤ (33124456498129/100000000000000 : ℝ)^3739
        have hw : |(4200608859/10000000000 : ℝ)|=(4200608859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744345213/2000000000 : ℝ)|^4763 ≤ (14195613625687/50000000000000 : ℝ)^3739
        have hw : |(744345213/2000000000 : ℝ)|=(744345213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118136433/250000000 : ℝ)|^4763 ≤ (38484316238881/100000000000000 : ℝ)^3739
        have hw : |(118136433/250000000 : ℝ)|=(118136433/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s1_4 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1686795703/10000000000 : ℝ)*x 0 + (5125470041/10000000000 : ℝ)*x 1 + (1381116323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686795703/10000000000 : ℝ)^4763 ≤ (10360437009041/100000000000000 : ℝ)^3739 := by
    have hnat : (1686795703 : ℕ)^4763*100000000000000^3739 ≤ 10360437009041^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686795703 10000000000 10360437009041 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125470041/10000000000 : ℝ)^4763 ≤ (1067034522891/2500000000000 : ℝ)^3739 := by
    have hnat : (5125470041 : ℕ)^4763*2500000000000^3739 ≤ 1067034522891^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125470041 10000000000 1067034522891 2500000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381116323/2500000000 : ℝ)^4763 ≤ (46958182051953/100000000000000 : ℝ)^3739 := by
    have hnat : (1381116323 : ℕ)^4763*100000000000000^3739 ≤ 46958182051953^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381116323 2500000000 46958182051953 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1686795703/10000000000 : ℝ), (5125470041/10000000000 : ℝ), (1381116323/2500000000 : ℝ)] ![(10360437009041/100000000000000 : ℝ), (1067034522891/2500000000000 : ℝ), (46958182051953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1686795703/10000000000 : ℝ)|^4763 ≤ (10360437009041/100000000000000 : ℝ)^3739
        have hw : |(-1686795703/10000000000 : ℝ)|=(1686795703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125470041/10000000000 : ℝ)|^4763 ≤ (1067034522891/2500000000000 : ℝ)^3739
        have hw : |(5125470041/10000000000 : ℝ)|=(5125470041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1381116323/2500000000 : ℝ)|^4763 ≤ (46958182051953/100000000000000 : ℝ)^3739
        have hw : |(1381116323/2500000000 : ℝ)|=(1381116323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s1_5 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210525181/400000000 : ℝ)*x 0 + (-299290309/2000000000 : ℝ)*x 1 + (690558203/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210525181/400000000 : ℝ)^4763 ≤ (11036749149347/25000000000000 : ℝ)^3739 := by
    have hnat : (210525181 : ℕ)^4763*25000000000000^3739 ≤ 11036749149347^3739*400000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210525181 400000000 11036749149347 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299290309/2000000000 : ℝ)^4763 ≤ (1111852218483/12500000000000 : ℝ)^3739 := by
    have hnat : (299290309 : ℕ)^4763*12500000000000^3739 ≤ 1111852218483^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299290309 2000000000 1111852218483 12500000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690558203/1250000000 : ℝ)^4763 ≤ (2934886602927/6250000000000 : ℝ)^3739 := by
    have hnat : (690558203 : ℕ)^4763*6250000000000^3739 ≤ 2934886602927^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690558203 1250000000 2934886602927 6250000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210525181/400000000 : ℝ), (-299290309/2000000000 : ℝ), (690558203/1250000000 : ℝ)] ![(11036749149347/25000000000000 : ℝ), (1111852218483/12500000000000 : ℝ), (2934886602927/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210525181/400000000 : ℝ)|^4763 ≤ (11036749149347/25000000000000 : ℝ)^3739
        have hw : |(210525181/400000000 : ℝ)|=(210525181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299290309/2000000000 : ℝ)|^4763 ≤ (1111852218483/12500000000000 : ℝ)^3739
        have hw : |(-299290309/2000000000 : ℝ)|=(299290309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(690558203/1250000000 : ℝ)|^4763 ≤ (2934886602927/6250000000000 : ℝ)^3739
        have hw : |(690558203/1250000000 : ℝ)|=(690558203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s1_6 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315782221/2500000000 : ℝ)*x 0 + (2762232933/5000000000 : ℝ)*x 1 + (-748226051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315782221/2500000000 : ℝ)^4763 ≤ (22073494874091/50000000000000 : ℝ)^3739 := by
    have hnat : (1315782221 : ℕ)^4763*50000000000000^3739 ≤ 22073494874091^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315782221 2500000000 22073494874091 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762232933/5000000000 : ℝ)^4763 ≤ (9391637653439/20000000000000 : ℝ)^3739 := by
    have hnat : (2762232933 : ℕ)^4763*20000000000000^3739 ≤ 9391637653439^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762232933 5000000000 9391637653439 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748226051/5000000000 : ℝ)^4763 ≤ (8894821965361/100000000000000 : ℝ)^3739 := by
    have hnat : (748226051 : ℕ)^4763*100000000000000^3739 ≤ 8894821965361^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748226051 5000000000 8894821965361 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315782221/2500000000 : ℝ), (2762232933/5000000000 : ℝ), (-748226051/5000000000 : ℝ)] ![(22073494874091/50000000000000 : ℝ), (9391637653439/20000000000000 : ℝ), (8894821965361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315782221/2500000000 : ℝ)|^4763 ≤ (22073494874091/50000000000000 : ℝ)^3739
        have hw : |(1315782221/2500000000 : ℝ)|=(1315782221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2762232933/5000000000 : ℝ)|^4763 ≤ (9391637653439/20000000000000 : ℝ)^3739
        have hw : |(2762232933/5000000000 : ℝ)|=(2762232933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748226051/5000000000 : ℝ)|^4763 ≤ (8894821965361/100000000000000 : ℝ)^3739
        have hw : |(-748226051/5000000000 : ℝ)|=(748226051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s1_7 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050287639/2500000000 : ℝ)*x 0 + (294659787/625000000 : ℝ)*x 1 + (3732795309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050287639/2500000000 : ℝ)^4763 ≤ (33129898087079/100000000000000 : ℝ)^3739 := by
    have hnat : (1050287639 : ℕ)^4763*100000000000000^3739 ≤ 33129898087079^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050287639 2500000000 33129898087079 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294659787/625000000 : ℝ)^4763 ≤ (38371262933479/100000000000000 : ℝ)^3739 := by
    have hnat : (294659787 : ℕ)^4763*100000000000000^3739 ≤ 38371262933479^3739*625000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294659787 625000000 38371262933479 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3732795309/10000000000 : ℝ)^4763 ≤ (28498838966497/100000000000000 : ℝ)^3739 := by
    have hnat : (3732795309 : ℕ)^4763*100000000000000^3739 ≤ 28498838966497^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732795309 10000000000 28498838966497 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050287639/2500000000 : ℝ), (294659787/625000000 : ℝ), (3732795309/10000000000 : ℝ)] ![(33129898087079/100000000000000 : ℝ), (38371262933479/100000000000000 : ℝ), (28498838966497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050287639/2500000000 : ℝ)|^4763 ≤ (33129898087079/100000000000000 : ℝ)^3739
        have hw : |(1050287639/2500000000 : ℝ)|=(1050287639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(294659787/625000000 : ℝ)|^4763 ≤ (38371262933479/100000000000000 : ℝ)^3739
        have hw : |(294659787/625000000 : ℝ)|=(294659787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3732795309/10000000000 : ℝ)|^4763 ≤ (28498838966497/100000000000000 : ℝ)^3739
        have hw : |(3732795309/10000000000 : ℝ)|=(3732795309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1611_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1011/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9149/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8897/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1011/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1011/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1011/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1011/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1011/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1011/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1011/25000 : ℝ) ^ (4759/1024 : ℝ) ≤ (33512685178489/100000000000000000000 : ℝ) := by
    have hpowers : (1011/25000 : ℝ)^4759 ≤ (33512685178489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1011 : ℕ)^4759*100000000000000000000^1024 ≤ 33512685178489^1024*25000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1011 25000 33512685178489 100000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1011/25000 : ℝ)) (X := (33512685178489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24219/100000 : ℝ) ^ (4759/1024 : ℝ) ≤ (137369408865349401/100000000000000000000 : ℝ) := by
    have hpowers : (24219/100000 : ℝ)^4759 ≤ (137369408865349401/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24219 : ℕ)^4759*100000000000000000000^1024 ≤ 137369408865349401^1024*100000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24219 100000 137369408865349401 100000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24219/100000 : ℝ)) (X := (137369408865349401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000033512685178489/50000000000000000000 : ℝ) ≤ (10000001442192923/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (50000033512685178489/50000000000000000000 : ℝ)^1024 ≤ (10000001442192923/10000000000000000 : ℝ)^4759 := by
      have hnat : (50000033512685178489 : ℕ)^1024*10000000000000000^4759 ≤ 10000001442192923^4759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000033512685178489 50000000000000000000 10000001442192923 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001442192923/10000000000000000 : ℝ)) (X := (50000033512685178489/50000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10013740292155052789/10000000000000000000 : ℝ) ≤ (10002954923081323/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (10013740292155052789/10000000000000000000 : ℝ)^1024 ≤ (10002954923081323/10000000000000000 : ℝ)^4759 := by
      have hnat : (10013740292155052789 : ℕ)^1024*10000000000000000^4759 ≤ 10002954923081323^4759*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013740292155052789 10000000000000000000 10002954923081323 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002954923081323/10000000000000000 : ℝ)) (X := (10013740292155052789/10000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50137369408865349401/50000000000000000000 : ℝ) ≤ (10005908403969723/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (50137369408865349401/50000000000000000000 : ℝ)^1024 ≤ (10005908403969723/10000000000000000 : ℝ)^4759 := by
      have hnat : (50137369408865349401 : ℕ)^1024*10000000000000000^4759 ≤ 10005908403969723^4759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50137369408865349401 50000000000000000000 10005908403969723 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005908403969723/10000000000000000 : ℝ)) (X := (50137369408865349401/50000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(33512685178489/100000000000000000000 : ℝ) ≤ ((2689681884570891231/2690000000000000000 : ℝ)+2*(7383702221/5043750000000 : ℝ)*(1011/25000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (2689681884570891231/2690000000000000000 : ℝ)+2*(7383702221/5043750000000 : ℝ)*(1011/25000 : ℝ)=(10000001442192923/10000000000000000 : ℝ) by norm_num, show 1+2*(33512685178489/100000000000000000000 : ℝ)=(50000033512685178489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(137369408865349401/100000000000000000000 : ℝ)+(33512685178489/100000000000000000000 : ℝ) ≤ ((2689681884570891231/2690000000000000000 : ℝ)+(7383702221/5043750000000 : ℝ)*((24219/100000 : ℝ)+(1011/25000 : ℝ)))^(4759/1024 : ℝ) := by
    rw [show (2689681884570891231/2690000000000000000 : ℝ)+(7383702221/5043750000000 : ℝ)*((24219/100000 : ℝ)+(1011/25000 : ℝ))=(10002954923081323/10000000000000000 : ℝ) by norm_num, show 1+(137369408865349401/100000000000000000000 : ℝ)+(33512685178489/100000000000000000000 : ℝ)=(10013740292155052789/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(137369408865349401/100000000000000000000 : ℝ) ≤ ((2689681884570891231/2690000000000000000 : ℝ)+2*(7383702221/5043750000000 : ℝ)*(24219/100000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (2689681884570891231/2690000000000000000 : ℝ)+2*(7383702221/5043750000000 : ℝ)*(24219/100000 : ℝ)=(10005908403969723/10000000000000000 : ℝ) by norm_num, show 1+2*(137369408865349401/100000000000000000000 : ℝ)=(50137369408865349401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2689681884570891231/2690000000000000000 : ℝ)*(X 1 0+X 2 0)+(7383702221/5043750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (1011/25000 : ℝ)) (hi := (24219/100000 : ℝ)) (c := (2689681884570891231/2690000000000000000 : ℝ)) (alpha := (7383702221/5043750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2689681884570891231/2690000000000000000 : ℝ)*(X 0 1+X 2 1)+(7383702221/5043750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (1011/25000 : ℝ)) (hi := (24219/100000 : ℝ)) (c := (2689681884570891231/2690000000000000000 : ℝ)) (alpha := (7383702221/5043750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2689681884570891231/2690000000000000000 : ℝ)*(X 0 2+X 1 2)+(7383702221/5043750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (1011/25000 : ℝ)) (hi := (24219/100000 : ℝ)) (c := (2689681884570891231/2690000000000000000 : ℝ)) (alpha := (7383702221/5043750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1686575009/10000000000 : ℝ)*X 0 0+(5528964347/10000000000 : ℝ)*X 0 1+(1024207881/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074332943/2000000000 : ℝ)*X 1 0+(-1899877931/10000000000 : ℝ)*X 1 1+(1024207851/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671458061/1250000000 : ℝ)*X 2 0+(640129927/1250000000 : ℝ)*X 2 1+(-949939011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200608859/10000000000 : ℝ)*X 0 0+(744345213/2000000000 : ℝ)*X 0 1+(118136433/250000000 : ℝ)*X 0 2+(4200608859/10000000000 : ℝ)*X 1 0+(744345213/2000000000 : ℝ)*X 1 1+(118136433/250000000 : ℝ)*X 1 2+(4200608859/10000000000 : ℝ)*X 2 0+(744345213/2000000000 : ℝ)*X 2 1+(118136433/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1686795703/10000000000 : ℝ)*X 0 0+(5125470041/10000000000 : ℝ)*X 0 1+(1381116323/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210525181/400000000 : ℝ)*X 1 0+(-299290309/2000000000 : ℝ)*X 1 1+(690558203/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315782221/2500000000 : ℝ)*X 2 0+(2762232933/5000000000 : ℝ)*X 2 1+(-748226051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050287639/2500000000 : ℝ)*X 0 0+(294659787/625000000 : ℝ)*X 0 1+(3732795309/10000000000 : ℝ)*X 0 2+(1050287639/2500000000 : ℝ)*X 1 0+(294659787/625000000 : ℝ)*X 1 1+(3732795309/10000000000 : ℝ)*X 1 2+(1050287639/2500000000 : ℝ)*X 2 0+(294659787/625000000 : ℝ)*X 2 1+(3732795309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43056718450505336260181713/33625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6244507/6250000000000 : ℝ)*(base1) + (64474619/12500000000000 : ℝ)*(base19) + (411992151/100000000000000 : ℝ)*(base23) + (34552653/50000000000000 : ℝ)*(upper3) + (430965364387859/25000000000000 : ℝ)*(major0) + (430965364387859/25000000000000 : ℝ)*(major1) + (430965364387859/25000000000000 : ℝ)*(major2) + (1225717547823729/50000000000000 : ℝ)*(sp0) + (76607400786827/3125000000000 : ℝ)*(sp1) + (1225718459293349/50000000000000 : ℝ)*(sp2) + (498141934730623/50000000000000 : ℝ)*(sp3) + (234524007/10000000000000 : ℝ)*(sp4) + (5198283/50000000000000 : ℝ)*(sp6) + (1562070851/100000000000000 : ℝ)*(sp7) + (99628553144421/10000000000000 : ℝ)*(f.failure) + (306429667621927/12500000000000 : ℝ)*(f.sum) + (8284150298933/2017500000000000000000000000 : ℝ)*base65 + (726519524038793287/201750000000000000000000000000000 : ℝ)*base67 + (692991868215456713/201750000000000000000000000000000 : ℝ)*base70 + (616904784247793287/201750000000000000000000000000000 : ℝ)*base71 + (4591371439883/2017500000000000000000000000 : ℝ)*base73 + (1095658921147956713/201750000000000000000000000000000 : ℝ)*base76 + (423609076033793287/201750000000000000000000000000000 : ℝ)*base77 + (815091460414793287/201750000000000000000000000000000 : ℝ)*base79 + (10269293229989/4035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1051547/125000000000000000000 : ℝ)*base89 + (1051547/125000000000000000000 : ℝ)*base91 + (1051547/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3781686116485961897151/336250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2190757683/100000000000000 : ℝ)*(base19) + (1903090413/100000000000000 : ℝ)*(base23) + (20267021/100000000000000 : ℝ)*(upper2) + (194837663/50000000000000 : ℝ)*(upper3) + (160402171/100000000000000 : ℝ)*(upper5) + (1762434621648759/100000000000000 : ℝ)*(major0) + (1762434621648759/100000000000000 : ℝ)*(major1) + (1762434621648759/100000000000000 : ℝ)*(major2) + (16707253169/100000000000000 : ℝ)*(sp1) + (3138427337/20000000000000 : ℝ)*(sp2) + (2506290428724663/100000000000000 : ℝ)*(sp4) + (250627153071381/10000000000000 : ℝ)*(sp5) + (626568208374391/25000000000000 : ℝ)*(sp6) + (1018578439684511/100000000000000 : ℝ)*(sp7) + (1018578439684511/100000000000000 : ℝ)*(f.failure) + (2506290428724663/100000000000000 : ℝ)*(f.sum) + (6309792344707/1345000000000000000000000000 : ℝ)*base66 + (1638221438019067671/269000000000000000000000000000000 : ℝ)*base68 + (206207243780932329/269000000000000000000000000000000 : ℝ)*base69 + (158006572133067671/269000000000000000000000000000000 : ℝ)*base72 + (6123350725827/1345000000000000000000000000 : ℝ)*base74 + (1650382180189932329/269000000000000000000000000000000 : ℝ)*base75 + (1035782831532067671/269000000000000000000000000000000 : ℝ)*base78 + (295241562911932329/269000000000000000000000000000000 : ℝ)*base79 + (1953985471763/1345000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4906177/1250000000000000000000 : ℝ)*base89 + (4906177/1250000000000000000000 : ℝ)*base91 + (4906177/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1611_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1011/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8897/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1611_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1611_s2_0 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68013617/400000000 : ℝ)*x 0 + (2733149043/5000000000 : ℝ)*x 1 + (1293673017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68013617/400000000 : ℝ)^4763 ≤ (10466530111783/100000000000000 : ℝ)^3739 := by
    have hnat : (68013617 : ℕ)^4763*100000000000000^3739 ≤ 10466530111783^3739*400000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68013617 400000000 10466530111783 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733149043/5000000000 : ℝ)^4763 ≤ (46329261008513/100000000000000 : ℝ)^3739 := by
    have hnat : (2733149043 : ℕ)^4763*100000000000000^3739 ≤ 46329261008513^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733149043 5000000000 46329261008513 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293673017/2500000000 : ℝ)^4763 ≤ (5400526107863/12500000000000 : ℝ)^3739 := by
    have hnat : (1293673017 : ℕ)^4763*12500000000000^3739 ≤ 5400526107863^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293673017 2500000000 5400526107863 12500000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68013617/400000000 : ℝ), (2733149043/5000000000 : ℝ), (1293673017/2500000000 : ℝ)] ![(10466530111783/100000000000000 : ℝ), (46329261008513/100000000000000 : ℝ), (5400526107863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68013617/400000000 : ℝ)|^4763 ≤ (10466530111783/100000000000000 : ℝ)^3739
        have hw : |(-68013617/400000000 : ℝ)|=(68013617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733149043/5000000000 : ℝ)|^4763 ≤ (46329261008513/100000000000000 : ℝ)^3739
        have hw : |(2733149043/5000000000 : ℝ)|=(2733149043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293673017/2500000000 : ℝ)|^4763 ≤ (5400526107863/12500000000000 : ℝ)^3739
        have hw : |(1293673017/2500000000 : ℝ)|=(1293673017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s2_1 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83676999/156250000 : ℝ)*x 0 + (-370183547/2000000000 : ℝ)*x 1 + (5174691947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83676999/156250000 : ℝ)^4763 ≤ (45134507323563/100000000000000 : ℝ)^3739 := by
    have hnat : (83676999 : ℕ)^4763*100000000000000^3739 ≤ 45134507323563^3739*156250000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83676999 156250000 45134507323563 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370183547/2000000000 : ℝ)^4763 ≤ (2332257016717/20000000000000 : ℝ)^3739 := by
    have hnat : (370183547 : ℕ)^4763*20000000000000^3739 ≤ 2332257016717^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370183547 2000000000 2332257016717 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174691947/10000000000 : ℝ)^4763 ≤ (43204207575983/100000000000000 : ℝ)^3739 := by
    have hnat : (5174691947 : ℕ)^4763*100000000000000^3739 ≤ 43204207575983^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174691947 10000000000 43204207575983 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83676999/156250000 : ℝ), (-370183547/2000000000 : ℝ), (5174691947/10000000000 : ℝ)] ![(45134507323563/100000000000000 : ℝ), (2332257016717/20000000000000 : ℝ), (43204207575983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83676999/156250000 : ℝ)|^4763 ≤ (45134507323563/100000000000000 : ℝ)^3739
        have hw : |(83676999/156250000 : ℝ)|=(83676999/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-370183547/2000000000 : ℝ)|^4763 ≤ (2332257016717/20000000000000 : ℝ)^3739
        have hw : |(-370183547/2000000000 : ℝ)|=(370183547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174691947/10000000000 : ℝ)|^4763 ≤ (43204207575983/100000000000000 : ℝ)^3739
        have hw : |(5174691947/10000000000 : ℝ)|=(5174691947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s2_2 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338831967/2500000000 : ℝ)*x 0 + (2587345991/5000000000 : ℝ)*x 1 + (-92545889/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338831967/2500000000 : ℝ)^4763 ≤ (22567253296753/50000000000000 : ℝ)^3739 := by
    have hnat : (1338831967 : ℕ)^4763*50000000000000^3739 ≤ 22567253296753^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338831967 2500000000 22567253296753 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587345991/5000000000 : ℝ)^4763 ≤ (43204207948233/100000000000000 : ℝ)^3739 := by
    have hnat : (2587345991 : ℕ)^4763*100000000000000^3739 ≤ 43204207948233^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587345991 5000000000 43204207948233 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92545889/500000000 : ℝ)^4763 ≤ (11661285444743/100000000000000 : ℝ)^3739 := by
    have hnat : (92545889 : ℕ)^4763*100000000000000^3739 ≤ 11661285444743^3739*500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92545889 500000000 11661285444743 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338831967/2500000000 : ℝ), (2587345991/5000000000 : ℝ), (-92545889/500000000 : ℝ)] ![(22567253296753/50000000000000 : ℝ), (43204207948233/100000000000000 : ℝ), (11661285444743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338831967/2500000000 : ℝ)|^4763 ≤ (22567253296753/50000000000000 : ℝ)^3739
        have hw : |(1338831967/2500000000 : ℝ)|=(1338831967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587345991/5000000000 : ℝ)|^4763 ≤ (43204207948233/100000000000000 : ℝ)^3739
        have hw : |(2587345991/5000000000 : ℝ)|=(2587345991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92545889/500000000 : ℝ)|^4763 ≤ (11661285444743/100000000000000 : ℝ)^3739
        have hw : |(-92545889/500000000 : ℝ)|=(92545889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s2_3 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4210770309/10000000000 : ℝ)*x 0 + (48296981/125000000 : ℝ)*x 1 + (4581277643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4210770309/10000000000 : ℝ)^4763 ≤ (664531296081/2000000000000 : ℝ)^3739 := by
    have hnat : (4210770309 : ℕ)^4763*2000000000000^3739 ≤ 664531296081^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210770309 10000000000 664531296081 2000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48296981/125000000 : ℝ)^4763 ≤ (2977860741883/10000000000000 : ℝ)^3739 := by
    have hnat : (48296981 : ℕ)^4763*10000000000000^3739 ≤ 2977860741883^3739*125000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48296981 125000000 2977860741883 10000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4581277643/10000000000 : ℝ)^4763 ≤ (18497413880833/50000000000000 : ℝ)^3739 := by
    have hnat : (4581277643 : ℕ)^4763*50000000000000^3739 ≤ 18497413880833^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581277643 10000000000 18497413880833 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4210770309/10000000000 : ℝ), (48296981/125000000 : ℝ), (4581277643/10000000000 : ℝ)] ![(664531296081/2000000000000 : ℝ), (2977860741883/10000000000000 : ℝ), (18497413880833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4210770309/10000000000 : ℝ)|^4763 ≤ (664531296081/2000000000000 : ℝ)^3739
        have hw : |(4210770309/10000000000 : ℝ)|=(4210770309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48296981/125000000 : ℝ)|^4763 ≤ (2977860741883/10000000000000 : ℝ)^3739
        have hw : |(48296981/125000000 : ℝ)|=(48296981/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4581277643/10000000000 : ℝ)|^4763 ≤ (18497413880833/50000000000000 : ℝ)^3739
        have hw : |(4581277643/10000000000 : ℝ)|=(4581277643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s2_4 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1700420817/10000000000 : ℝ)*x 0 + (258848171/500000000 : ℝ)*x 1 + (683000241/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1700420817/10000000000 : ℝ)^4763 ≤ (5233580249653/50000000000000 : ℝ)^3739 := by
    have hnat : (1700420817 : ℕ)^4763*50000000000000^3739 ≤ 5233580249653^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700420817 10000000000 5233580249653 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258848171/500000000 : ℝ)^4763 ≤ (43228367765661/100000000000000 : ℝ)^3739 := by
    have hnat : (258848171 : ℕ)^4763*100000000000000^3739 ≤ 43228367765661^3739*500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258848171 500000000 43228367765661 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683000241/1250000000 : ℝ)^4763 ≤ (23152235862823/50000000000000 : ℝ)^3739 := by
    have hnat : (683000241 : ℕ)^4763*50000000000000^3739 ≤ 23152235862823^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683000241 1250000000 23152235862823 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1700420817/10000000000 : ℝ), (258848171/500000000 : ℝ), (683000241/1250000000 : ℝ)] ![(5233580249653/50000000000000 : ℝ), (43228367765661/100000000000000 : ℝ), (23152235862823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1700420817/10000000000 : ℝ)|^4763 ≤ (5233580249653/50000000000000 : ℝ)^3739
        have hw : |(-1700420817/10000000000 : ℝ)|=(1700420817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258848171/500000000 : ℝ)|^4763 ≤ (43228367765661/100000000000000 : ℝ)^3739
        have hw : |(258848171/500000000 : ℝ)|=(258848171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683000241/1250000000 : ℝ)|^4763 ≤ (23152235862823/50000000000000 : ℝ)^3739
        have hw : |(683000241/1250000000 : ℝ)|=(683000241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s2_5 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319464783/2500000000 : ℝ)*x 0 + (-780803937/5000000000 : ℝ)*x 1 + (546400219/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319464783/2500000000 : ℝ)^4763 ≤ (443044455123/1000000000000 : ℝ)^3739 := by
    have hnat : (1319464783 : ℕ)^4763*1000000000000^3739 ≤ 443044455123^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319464783 2500000000 443044455123 1000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (780803937/5000000000 : ℝ)^4763 ≤ (939107990899/10000000000000 : ℝ)^3739 := by
    have hnat : (780803937 : ℕ)^4763*10000000000000^3739 ≤ 939107990899^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780803937 5000000000 939107990899 10000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546400219/1000000000 : ℝ)^4763 ≤ (46304474554031/100000000000000 : ℝ)^3739 := by
    have hnat : (546400219 : ℕ)^4763*100000000000000^3739 ≤ 46304474554031^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546400219 1000000000 46304474554031 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319464783/2500000000 : ℝ), (-780803937/5000000000 : ℝ), (546400219/1000000000 : ℝ)] ![(443044455123/1000000000000 : ℝ), (939107990899/10000000000000 : ℝ), (46304474554031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319464783/2500000000 : ℝ)|^4763 ≤ (443044455123/1000000000000 : ℝ)^3739
        have hw : |(1319464783/2500000000 : ℝ)|=(1319464783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-780803937/5000000000 : ℝ)|^4763 ≤ (939107990899/10000000000000 : ℝ)^3739
        have hw : |(-780803937/5000000000 : ℝ)|=(780803937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546400219/1000000000 : ℝ)|^4763 ≤ (46304474554031/100000000000000 : ℝ)^3739
        have hw : |(546400219/1000000000 : ℝ)|=(546400219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s2_6 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638929881/5000000000 : ℝ)*x 0 + (546400141/1000000000 : ℝ)*x 1 + (-780804047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638929881/5000000000 : ℝ)^4763 ≤ (11076113062281/25000000000000 : ℝ)^3739 := by
    have hnat : (2638929881 : ℕ)^4763*25000000000000^3739 ≤ 11076113062281^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638929881 5000000000 11076113062281 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546400141/1000000000 : ℝ)^4763 ≤ (46304466133649/100000000000000 : ℝ)^3739 := by
    have hnat : (546400141 : ℕ)^4763*100000000000000^3739 ≤ 46304466133649^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546400141 1000000000 46304466133649 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780804047/5000000000 : ℝ)^4763 ≤ (1878216318869/20000000000000 : ℝ)^3739 := by
    have hnat : (780804047 : ℕ)^4763*20000000000000^3739 ≤ 1878216318869^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780804047 5000000000 1878216318869 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638929881/5000000000 : ℝ), (546400141/1000000000 : ℝ), (-780804047/5000000000 : ℝ)] ![(11076113062281/25000000000000 : ℝ), (46304466133649/100000000000000 : ℝ), (1878216318869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638929881/5000000000 : ℝ)|^4763 ≤ (11076113062281/25000000000000 : ℝ)^3739
        have hw : |(2638929881/5000000000 : ℝ)|=(2638929881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546400141/1000000000 : ℝ)|^4763 ≤ (46304466133649/100000000000000 : ℝ)^3739
        have hw : |(546400141/1000000000 : ℝ)|=(546400141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-780804047/5000000000 : ℝ)|^4763 ≤ (1878216318869/20000000000000 : ℝ)^3739
        have hw : |(-780804047/5000000000 : ℝ)|=(780804047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s2_7 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52637109/125000000 : ℝ)*x 0 + (2287844527/5000000000 : ℝ)*x 1 + (773881741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52637109/125000000 : ℝ)^4763 ≤ (6645711845669/20000000000000 : ℝ)^3739 := by
    have hnat : (52637109 : ℕ)^4763*20000000000000^3739 ≤ 6645711845669^3739*125000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52637109 125000000 6645711845669 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287844527/5000000000 : ℝ)^4763 ≤ (36937348773881/100000000000000 : ℝ)^3739 := by
    have hnat : (2287844527 : ℕ)^4763*100000000000000^3739 ≤ 36937348773881^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287844527 5000000000 36937348773881 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773881741/2000000000 : ℝ)^4763 ≤ (7458522996401/25000000000000 : ℝ)^3739 := by
    have hnat : (773881741 : ℕ)^4763*25000000000000^3739 ≤ 7458522996401^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773881741 2000000000 7458522996401 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52637109/125000000 : ℝ), (2287844527/5000000000 : ℝ), (773881741/2000000000 : ℝ)] ![(6645711845669/20000000000000 : ℝ), (36937348773881/100000000000000 : ℝ), (7458522996401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52637109/125000000 : ℝ)|^4763 ≤ (6645711845669/20000000000000 : ℝ)^3739
        have hw : |(52637109/125000000 : ℝ)|=(52637109/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2287844527/5000000000 : ℝ)|^4763 ≤ (36937348773881/100000000000000 : ℝ)^3739
        have hw : |(2287844527/5000000000 : ℝ)|=(2287844527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773881741/2000000000 : ℝ)|^4763 ≤ (7458522996401/25000000000000 : ℝ)^3739
        have hw : |(773881741/2000000000 : ℝ)|=(773881741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1611_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8897/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1649/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8897/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8897/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8897/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8897/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8897/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8897/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9149/100000 : ℝ) ^ (4759/1024 : ℝ) ≤ (744722559537801/50000000000000000000 : ℝ) := by
    have hpowers : (9149/100000 : ℝ)^4759 ≤ (744722559537801/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9149 : ℕ)^4759*50000000000000000000^1024 ≤ 744722559537801^1024*100000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9149 100000 744722559537801 50000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9149/100000 : ℝ)) (X := (744722559537801/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8897/50000 : ℝ) ^ (4759/1024 : ℝ) ≤ (32785044554367193/100000000000000000000 : ℝ) := by
    have hpowers : (8897/50000 : ℝ)^4759 ≤ (32785044554367193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8897 : ℕ)^4759*100000000000000000000^1024 ≤ 32785044554367193^1024*50000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8897 50000 32785044554367193 100000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8897/50000 : ℝ)) (X := (32785044554367193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000744722559537801/25000000000000000000 : ℝ) ≤ (1000006409640569/1000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (25000744722559537801/25000000000000000000 : ℝ)^1024 ≤ (1000006409640569/1000000000000000 : ℝ)^4759 := by
      have hnat : (25000744722559537801 : ℕ)^1024*1000000000000000^4759 ≤ 1000006409640569^4759*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000744722559537801 25000000000000000000 1000006409640569 1000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000006409640569/1000000000000000 : ℝ)) (X := (25000744722559537801/25000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006854897934688559/20000000000000000000 : ℝ) ≤ (2500184347330849/2500000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (20006854897934688559/20000000000000000000 : ℝ)^1024 ≤ (2500184347330849/2500000000000000 : ℝ)^4759 := by
      have hnat : (20006854897934688559 : ℕ)^1024*2500000000000000^4759 ≤ 2500184347330849^4759*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006854897934688559 20000000000000000000 2500184347330849 2500000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184347330849/2500000000000000 : ℝ)) (X := (20006854897934688559/20000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032785044554367193/50000000000000000000 : ℝ) ≤ (5000705341120551/5000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (50032785044554367193/50000000000000000000 : ℝ)^1024 ≤ (5000705341120551/5000000000000000 : ℝ)^4759 := by
      have hnat : (50032785044554367193 : ℕ)^1024*5000000000000000^4759 ≤ 5000705341120551^4759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032785044554367193 50000000000000000000 5000705341120551 5000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000705341120551/5000000000000000 : ℝ)) (X := (50032785044554367193/50000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(744722559537801/50000000000000000000 : ℝ) ≤ ((6174159585687071833/6175000000000000000 : ℝ)+2*(336646458853/432250000000000 : ℝ)*(9149/100000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (6174159585687071833/6175000000000000000 : ℝ)+2*(336646458853/432250000000000 : ℝ)*(9149/100000 : ℝ)=(1000006409640569/1000000000000000 : ℝ) by norm_num, show 1+2*(744722559537801/50000000000000000000 : ℝ)=(25000744722559537801/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32785044554367193/100000000000000000000 : ℝ)+(744722559537801/50000000000000000000 : ℝ) ≤ ((6174159585687071833/6175000000000000000 : ℝ)+(336646458853/432250000000000 : ℝ)*((8897/50000 : ℝ)+(9149/100000 : ℝ)))^(4759/1024 : ℝ) := by
    rw [show (6174159585687071833/6175000000000000000 : ℝ)+(336646458853/432250000000000 : ℝ)*((8897/50000 : ℝ)+(9149/100000 : ℝ))=(2500184347330849/2500000000000000 : ℝ) by norm_num, show 1+(32785044554367193/100000000000000000000 : ℝ)+(744722559537801/50000000000000000000 : ℝ)=(20006854897934688559/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32785044554367193/100000000000000000000 : ℝ) ≤ ((6174159585687071833/6175000000000000000 : ℝ)+2*(336646458853/432250000000000 : ℝ)*(8897/50000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (6174159585687071833/6175000000000000000 : ℝ)+2*(336646458853/432250000000000 : ℝ)*(8897/50000 : ℝ)=(5000705341120551/5000000000000000 : ℝ) by norm_num, show 1+2*(32785044554367193/100000000000000000000 : ℝ)=(50032785044554367193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6174159585687071833/6175000000000000000 : ℝ)*(X 1 0+X 2 0)+(336646458853/432250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (9149/100000 : ℝ)) (hi := (8897/50000 : ℝ)) (c := (6174159585687071833/6175000000000000000 : ℝ)) (alpha := (336646458853/432250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6174159585687071833/6175000000000000000 : ℝ)*(X 0 1+X 2 1)+(336646458853/432250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (9149/100000 : ℝ)) (hi := (8897/50000 : ℝ)) (c := (6174159585687071833/6175000000000000000 : ℝ)) (alpha := (336646458853/432250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6174159585687071833/6175000000000000000 : ℝ)*(X 0 2+X 1 2)+(336646458853/432250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (9149/100000 : ℝ)) (hi := (8897/50000 : ℝ)) (c := (6174159585687071833/6175000000000000000 : ℝ)) (alpha := (336646458853/432250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-68013617/400000000 : ℝ)*X 0 0+(2733149043/5000000000 : ℝ)*X 0 1+(1293673017/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83676999/156250000 : ℝ)*X 1 0+(-370183547/2000000000 : ℝ)*X 1 1+(5174691947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338831967/2500000000 : ℝ)*X 2 0+(2587345991/5000000000 : ℝ)*X 2 1+(-92545889/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4210770309/10000000000 : ℝ)*X 0 0+(48296981/125000000 : ℝ)*X 0 1+(4581277643/10000000000 : ℝ)*X 0 2+(4210770309/10000000000 : ℝ)*X 1 0+(48296981/125000000 : ℝ)*X 1 1+(4581277643/10000000000 : ℝ)*X 1 2+(4210770309/10000000000 : ℝ)*X 2 0+(48296981/125000000 : ℝ)*X 2 1+(4581277643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1700420817/10000000000 : ℝ)*X 0 0+(258848171/500000000 : ℝ)*X 0 1+(683000241/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319464783/2500000000 : ℝ)*X 1 0+(-780803937/5000000000 : ℝ)*X 1 1+(546400219/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638929881/5000000000 : ℝ)*X 2 0+(546400141/1000000000 : ℝ)*X 2 1+(-780804047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((52637109/125000000 : ℝ)*X 0 0+(2287844527/5000000000 : ℝ)*X 0 1+(773881741/2000000000 : ℝ)*X 0 2+(52637109/125000000 : ℝ)*X 1 0+(2287844527/5000000000 : ℝ)*X 1 1+(773881741/2000000000 : ℝ)*X 1 2+(52637109/125000000 : ℝ)*X 2 0+(2287844527/5000000000 : ℝ)*X 2 1+(773881741/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18376714459815635637147679179/2161250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (397728871/25000000000000 : ℝ)*(base19) + (4737139/312500000000 : ℝ)*(base23) + (16862197/100000000000000 : ℝ)*(lower2) + (112576711/50000000000000 : ℝ)*(upper3) + (80961629/50000000000000 : ℝ)*(upper5) + (2411513124770903/100000000000000 : ℝ)*(major0) + (2411513124770903/100000000000000 : ℝ)*(major1) + (2411513124770903/100000000000000 : ℝ)*(major2) + (857325723230511/25000000000000 : ℝ)*(sp0) + (857329654921429/25000000000000 : ℝ)*(sp1) + (42866483683959/1250000000000 : ℝ)*(sp2) + (696849040745141/50000000000000 : ℝ)*(sp3) + (17317679157/100000000000000 : ℝ)*(sp4) + (7674023067/100000000000000 : ℝ)*(sp7) + (348426438878337/25000000000000 : ℝ)*(f.failure) + (8573300526503/250000000000 : ℝ)*(f.sum) + (4519862095507/43225000000000000000000000000 : ℝ)*base66 + (29136581009764173607/4322500000000000000000000000000000 : ℝ)*base68 + (39240340674171673607/4322500000000000000000000000000000 : ℝ)*base70 + (29306104497534173607/4322500000000000000000000000000000 : ℝ)*base72 + (5251668740371/5403125000000000000000000000 : ℝ)*base73 + (11116285605061673607/4322500000000000000000000000000000 : ℝ)*base76 + (11556256838625826393/4322500000000000000000000000000000 : ℝ)*base77 + (15836894809325826393/4322500000000000000000000000000000 : ℝ)*base79 + (204272120455707/43225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (88441/312500000000000000000 : ℝ)*base90 + (88441/312500000000000000000 : ℝ)*base92 + (88441/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104227614510197518747111077/8312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1570799699/100000000000000 : ℝ)*(base19) + (139517101/6250000000000 : ℝ)*(base23) + (221316779/100000000000000 : ℝ)*(upper3) + (62110397/50000000000000 : ℝ)*(lower4) + (112574373/50000000000000 : ℝ)*(upper5) + (122493044540619/5000000000000 : ℝ)*(major0) + (122493044540619/5000000000000 : ℝ)*(major1) + (122493044540619/5000000000000 : ℝ)*(major2) + (20133216241/100000000000000 : ℝ)*(sp1) + (20832165933/100000000000000 : ℝ)*(sp2) + (696770593216243/20000000000000 : ℝ)*(sp4) + (870957815516319/25000000000000 : ℝ)*(sp5) + (1741914950820833/50000000000000 : ℝ)*(sp6) + (44245887424631/3125000000000 : ℝ)*(sp7) + (44245887424631/3125000000000 : ℝ)*(f.failure) + (696770593216243/20000000000000 : ℝ)*(f.sum) + (46335869997731/8645000000000000000000000000 : ℝ)*base65 + (2047014238820807611/216125000000000000000000000000000 : ℝ)*base68 + (2026955291139307611/216125000000000000000000000000000 : ℝ)*base70 + (888726358298307611/216125000000000000000000000000000 : ℝ)*base72 + (18664427662749/8645000000000000000000000000 : ℝ)*base74 + (2920563686284682611/216125000000000000000000000000000 : ℝ)*base76 + (769048291062307611/216125000000000000000000000000000 : ℝ)*base78 + (906575124847557611/216125000000000000000000000000000 : ℝ)*base80 + (2266902406467/1080625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (81517/39062500000000000000 : ℝ)*base89 + (81517/39062500000000000000 : ℝ)*base91 + (81517/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1611_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8897/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1649/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1611_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1611_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1649/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1611_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1611_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1611_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1649/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1611_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
