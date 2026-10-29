-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1601_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:06.513522+00:00
-- url     : https://prove2.me/submissions/3bb2dbcf-79f0-45af-ac82-d802bbae20ca

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
theorem support_rectangle_w1601_s0_0 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1582677943/10000000000 : ℝ)*x 0 + (1462357433/2500000000 : ℝ)*x 1 + (122154969/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1582677943/10000000000 : ℝ)^4723 ≤ (2375194266617/25000000000000 : ℝ)^3699 := by
    have hnat : (1582677943 : ℕ)^4723*25000000000000^3699 ≤ 2375194266617^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582677943 10000000000 2375194266617 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1462357433/2500000000 : ℝ)^4723 ≤ (25212342810079/50000000000000 : ℝ)^3699 := by
    have hnat : (1462357433 : ℕ)^4723*50000000000000^3699 ≤ 25212342810079^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1462357433 2500000000 25212342810079 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122154969/250000000 : ℝ)^4723 ≤ (8014907458727/20000000000000 : ℝ)^3699 := by
    have hnat : (122154969 : ℕ)^4723*20000000000000^3699 ≤ 8014907458727^3699*250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122154969 250000000 8014907458727 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1582677943/10000000000 : ℝ), (1462357433/2500000000 : ℝ), (122154969/250000000 : ℝ)] ![(2375194266617/25000000000000 : ℝ), (25212342810079/50000000000000 : ℝ), (8014907458727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1582677943/10000000000 : ℝ)|^4723 ≤ (2375194266617/25000000000000 : ℝ)^3699
        have hw : |(-1582677943/10000000000 : ℝ)|=(1582677943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1462357433/2500000000 : ℝ)|^4723 ≤ (25212342810079/50000000000000 : ℝ)^3699
        have hw : |(1462357433/2500000000 : ℝ)|=(1462357433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122154969/250000000 : ℝ)|^4723 ≤ (8014907458727/20000000000000 : ℝ)^3699
        have hw : |(122154969/250000000 : ℝ)|=(122154969/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s0_1 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2728721217/5000000000 : ℝ)*x 0 + (-2117080803/10000000000 : ℝ)*x 1 + (610774827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2728721217/5000000000 : ℝ)^4723 ≤ (46150823938763/100000000000000 : ℝ)^3699 := by
    have hnat : (2728721217 : ℕ)^4723*100000000000000^3699 ≤ 46150823938763^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728721217 5000000000 46150823938763 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117080803/10000000000 : ℝ)^4723 ≤ (6887320125631/50000000000000 : ℝ)^3699 := by
    have hnat : (2117080803 : ℕ)^4723*50000000000000^3699 ≤ 6887320125631^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117080803 10000000000 6887320125631 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610774827/1250000000 : ℝ)^4723 ≤ (20037267892831/50000000000000 : ℝ)^3699 := by
    have hnat : (610774827 : ℕ)^4723*50000000000000^3699 ≤ 20037267892831^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610774827 1250000000 20037267892831 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2728721217/5000000000 : ℝ), (-2117080803/10000000000 : ℝ), (610774827/1250000000 : ℝ)] ![(46150823938763/100000000000000 : ℝ), (6887320125631/50000000000000 : ℝ), (20037267892831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2728721217/5000000000 : ℝ)|^4723 ≤ (46150823938763/100000000000000 : ℝ)^3699
        have hw : |(2728721217/5000000000 : ℝ)|=(2728721217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117080803/10000000000 : ℝ)|^4723 ≤ (6887320125631/50000000000000 : ℝ)^3699
        have hw : |(-2117080803/10000000000 : ℝ)|=(2117080803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(610774827/1250000000 : ℝ)|^4723 ≤ (20037267892831/50000000000000 : ℝ)^3699
        have hw : |(610774827/1250000000 : ℝ)|=(610774827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s0_2 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2728721167/5000000000 : ℝ)*x 0 + (977239731/2000000000 : ℝ)*x 1 + (-423416177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2728721167/5000000000 : ℝ)^4723 ≤ (46150822859011/100000000000000 : ℝ)^3699 := by
    have hnat : (2728721167 : ℕ)^4723*100000000000000^3699 ≤ 46150822859011^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728721167 5000000000 46150822859011 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977239731/2000000000 : ℝ)^4723 ≤ (40074536194071/100000000000000 : ℝ)^3699 := by
    have hnat : (977239731 : ℕ)^4723*100000000000000^3699 ≤ 40074536194071^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977239731 2000000000 40074536194071 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423416177/2000000000 : ℝ)^4723 ≤ (13774640932487/100000000000000 : ℝ)^3699 := by
    have hnat : (423416177 : ℕ)^4723*100000000000000^3699 ≤ 13774640932487^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423416177 2000000000 13774640932487 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2728721167/5000000000 : ℝ), (977239731/2000000000 : ℝ), (-423416177/2000000000 : ℝ)] ![(46150822859011/100000000000000 : ℝ), (40074536194071/100000000000000 : ℝ), (13774640932487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2728721167/5000000000 : ℝ)|^4723 ≤ (46150822859011/100000000000000 : ℝ)^3699
        have hw : |(2728721167/5000000000 : ℝ)|=(2728721167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977239731/2000000000 : ℝ)|^4723 ≤ (40074536194071/100000000000000 : ℝ)^3699
        have hw : |(977239731/2000000000 : ℝ)|=(977239731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423416177/2000000000 : ℝ)|^4723 ≤ (13774640932487/100000000000000 : ℝ)^3699
        have hw : |(-423416177/2000000000 : ℝ)|=(423416177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s0_3 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20571113/50000000 : ℝ)*x 0 + (307292249/1000000000 : ℝ)*x 1 + (2705942109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20571113/50000000 : ℝ)^4723 ≤ (32174400627031/100000000000000 : ℝ)^3699 := by
    have hnat : (20571113 : ℕ)^4723*100000000000000^3699 ≤ 32174400627031^3699*50000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20571113 50000000 32174400627031 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307292249/1000000000 : ℝ)^4723 ≤ (2216612149651/10000000000000 : ℝ)^3699 := by
    have hnat : (307292249 : ℕ)^4723*10000000000000^3699 ≤ 2216612149651^3699*1000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307292249 1000000000 2216612149651 10000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705942109/5000000000 : ℝ)^4723 ≤ (45659477859471/100000000000000 : ℝ)^3699 := by
    have hnat : (2705942109 : ℕ)^4723*100000000000000^3699 ≤ 45659477859471^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705942109 5000000000 45659477859471 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20571113/50000000 : ℝ), (307292249/1000000000 : ℝ), (2705942109/5000000000 : ℝ)] ![(32174400627031/100000000000000 : ℝ), (2216612149651/10000000000000 : ℝ), (45659477859471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20571113/50000000 : ℝ)|^4723 ≤ (32174400627031/100000000000000 : ℝ)^3699
        have hw : |(20571113/50000000 : ℝ)|=(20571113/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307292249/1000000000 : ℝ)|^4723 ≤ (2216612149651/10000000000000 : ℝ)^3699
        have hw : |(307292249/1000000000 : ℝ)|=(307292249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705942109/5000000000 : ℝ)|^4723 ≤ (45659477859471/100000000000000 : ℝ)^3699
        have hw : |(2705942109/5000000000 : ℝ)|=(2705942109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s0_4 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-317119231/2000000000 : ℝ)*x 0 + (2455340881/5000000000 : ℝ)*x 1 + (5824072333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317119231/2000000000 : ℝ)^4723 ≤ (9523150251123/100000000000000 : ℝ)^3699 := by
    have hnat : (317119231 : ℕ)^4723*100000000000000^3699 ≤ 9523150251123^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317119231 2000000000 9523150251123 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2455340881/5000000000 : ℝ)^4723 ≤ (2520693856351/6250000000000 : ℝ)^3699 := by
    have hnat : (2455340881 : ℕ)^4723*6250000000000^3699 ≤ 2520693856351^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455340881 5000000000 2520693856351 6250000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5824072333/10000000000 : ℝ)^4723 ≤ (3134109251803/6250000000000 : ℝ)^3699 := by
    have hnat : (5824072333 : ℕ)^4723*6250000000000^3699 ≤ 3134109251803^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5824072333 10000000000 3134109251803 6250000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-317119231/2000000000 : ℝ), (2455340881/5000000000 : ℝ), (5824072333/10000000000 : ℝ)] ![(9523150251123/100000000000000 : ℝ), (2520693856351/6250000000000 : ℝ), (3134109251803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-317119231/2000000000 : ℝ)|^4723 ≤ (9523150251123/100000000000000 : ℝ)^3699
        have hw : |(-317119231/2000000000 : ℝ)|=(317119231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2455340881/5000000000 : ℝ)|^4723 ≤ (2520693856351/6250000000000 : ℝ)^3699
        have hw : |(2455340881/5000000000 : ℝ)|=(2455340881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5824072333/10000000000 : ℝ)|^4723 ≤ (3134109251803/6250000000000 : ℝ)^3699
        have hw : |(5824072333/10000000000 : ℝ)|=(5824072333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s0_5 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038870897/2000000000 : ℝ)*x 0 + (-147400821/1250000000 : ℝ)*x 1 + (5824072589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038870897/2000000000 : ℝ)^4723 ≤ (10832326787683/25000000000000 : ℝ)^3699 := by
    have hnat : (1038870897 : ℕ)^4723*25000000000000^3699 ≤ 10832326787683^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038870897 2000000000 10832326787683 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147400821/1250000000 : ℝ)^4723 ≤ (6524941995681/100000000000000 : ℝ)^3699 := by
    have hnat : (147400821 : ℕ)^4723*100000000000000^3699 ≤ 6524941995681^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147400821 1250000000 6524941995681 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5824072589/10000000000 : ℝ)^4723 ≤ (50145750843217/100000000000000 : ℝ)^3699 := by
    have hnat : (5824072589 : ℕ)^4723*100000000000000^3699 ≤ 50145750843217^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5824072589 10000000000 50145750843217 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038870897/2000000000 : ℝ), (-147400821/1250000000 : ℝ), (5824072589/10000000000 : ℝ)] ![(10832326787683/25000000000000 : ℝ), (6524941995681/100000000000000 : ℝ), (50145750843217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038870897/2000000000 : ℝ)|^4723 ≤ (10832326787683/25000000000000 : ℝ)^3699
        have hw : |(1038870897/2000000000 : ℝ)|=(1038870897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147400821/1250000000 : ℝ)|^4723 ≤ (6524941995681/100000000000000 : ℝ)^3699
        have hw : |(-147400821/1250000000 : ℝ)|=(147400821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5824072589/10000000000 : ℝ)|^4723 ≤ (50145750843217/100000000000000 : ℝ)^3699
        have hw : |(5824072589/10000000000 : ℝ)|=(5824072589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s0_6 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597177277/5000000000 : ℝ)*x 0 + (1164814471/2000000000 : ℝ)*x 1 + (-294801707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597177277/5000000000 : ℝ)^4723 ≤ (1083232697141/2500000000000 : ℝ)^3699 := by
    have hnat : (2597177277 : ℕ)^4723*2500000000000^3699 ≤ 1083232697141^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597177277 5000000000 1083232697141 2500000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164814471/2000000000 : ℝ)^4723 ≤ (12536437067677/25000000000000 : ℝ)^3699 := by
    have hnat : (1164814471 : ℕ)^4723*25000000000000^3699 ≤ 12536437067677^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164814471 2000000000 12536437067677 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294801707/2500000000 : ℝ)^4723 ≤ (815617979077/12500000000000 : ℝ)^3699 := by
    have hnat : (294801707 : ℕ)^4723*12500000000000^3699 ≤ 815617979077^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294801707 2500000000 815617979077 12500000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597177277/5000000000 : ℝ), (1164814471/2000000000 : ℝ), (-294801707/2500000000 : ℝ)] ![(1083232697141/2500000000000 : ℝ), (12536437067677/25000000000000 : ℝ), (815617979077/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597177277/5000000000 : ℝ)|^4723 ≤ (1083232697141/2500000000000 : ℝ)^3699
        have hw : |(2597177277/5000000000 : ℝ)|=(2597177277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1164814471/2000000000 : ℝ)|^4723 ≤ (12536437067677/25000000000000 : ℝ)^3699
        have hw : |(1164814471/2000000000 : ℝ)|=(1164814471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-294801707/2500000000 : ℝ)|^4723 ≤ (815617979077/12500000000000 : ℝ)^3699
        have hw : |(-294801707/2500000000 : ℝ)|=(294801707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s0_7 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (515163711/1250000000 : ℝ)*x 0 + (5352433627/10000000000 : ℝ)*x 1 + (3134495841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515163711/1250000000 : ℝ)^4723 ≤ (503830990731/1562500000000 : ℝ)^3699 := by
    have hnat : (515163711 : ℕ)^4723*1562500000000^3699 ≤ 503830990731^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515163711 1250000000 503830990731 1562500000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5352433627/10000000000 : ℝ)^4723 ≤ (22510011702367/50000000000000 : ℝ)^3699 := by
    have hnat : (5352433627 : ℕ)^4723*50000000000000^3699 ≤ 22510011702367^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352433627 10000000000 22510011702367 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134495841/10000000000 : ℝ)^4723 ≤ (5683698293801/25000000000000 : ℝ)^3699 := by
    have hnat : (3134495841 : ℕ)^4723*25000000000000^3699 ≤ 5683698293801^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134495841 10000000000 5683698293801 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515163711/1250000000 : ℝ), (5352433627/10000000000 : ℝ), (3134495841/10000000000 : ℝ)] ![(503830990731/1562500000000 : ℝ), (22510011702367/50000000000000 : ℝ), (5683698293801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515163711/1250000000 : ℝ)|^4723 ≤ (503830990731/1562500000000 : ℝ)^3699
        have hw : |(515163711/1250000000 : ℝ)|=(515163711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5352433627/10000000000 : ℝ)|^4723 ≤ (22510011702367/50000000000000 : ℝ)^3699
        have hw : |(5352433627/10000000000 : ℝ)|=(5352433627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134495841/10000000000 : ℝ)|^4723 ≤ (5683698293801/25000000000000 : ℝ)^3699
        have hw : |(3134495841/10000000000 : ℝ)|=(3134495841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1601_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (239/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24451/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4719/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4719 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4719*1^1024 ≤ 0^1024*1^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4719/1024 : ℝ) ≤ (1465999714802986201/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4719 ≤ (1465999714802986201/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4719*100000000000000000000^1024 ≤ 1465999714802986201^1024*5^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1465999714802986201 100000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1465999714802986201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4719 := by
      have hnat : (1 : ℕ)^1024*1^4719 ≤ 1^4719*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101465999714802986201/100000000000000000000 : ℝ) ≤ (10031630474467171/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (101465999714802986201/100000000000000000000 : ℝ)^1024 ≤ (10031630474467171/10000000000000000 : ℝ)^4719 := by
      have hnat : (101465999714802986201 : ℕ)^1024*10000000000000000^4719 ≤ 10031630474467171^4719*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101465999714802986201 100000000000000000000 10031630474467171 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10031630474467171/10000000000000000 : ℝ)) (X := (101465999714802986201/100000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51465999714802986201/50000000000000000000 : ℝ) ≤ (5031630474467171/5000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (51465999714802986201/50000000000000000000 : ℝ)^1024 ≤ (5031630474467171/5000000000000000 : ℝ)^4719 := by
      have hnat : (51465999714802986201 : ℕ)^1024*5000000000000000^4719 ≤ 5031630474467171^4719*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51465999714802986201 50000000000000000000 5031630474467171 5000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5031630474467171/5000000000000000 : ℝ)) (X := (51465999714802986201/50000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(31630474467171/4000000000000000 : ℝ)*(0 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31630474467171/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1465999714802986201/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(31630474467171/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4719/1024 : ℝ) := by
    rw [show (1 : ℝ)+(31630474467171/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10031630474467171/10000000000000000 : ℝ) by norm_num, show 1+(1465999714802986201/100000000000000000000 : ℝ)+(0 : ℝ)=(101465999714802986201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1465999714802986201/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(31630474467171/4000000000000000 : ℝ)*(2/5 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31630474467171/4000000000000000 : ℝ)*(2/5 : ℝ)=(5031630474467171/5000000000000000 : ℝ) by norm_num, show 1+2*(1465999714802986201/100000000000000000000 : ℝ)=(51465999714802986201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(31630474467171/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31630474467171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(31630474467171/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31630474467171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(31630474467171/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31630474467171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1582677943/10000000000 : ℝ)*X 0 0+(1462357433/2500000000 : ℝ)*X 0 1+(122154969/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2728721217/5000000000 : ℝ)*X 1 0+(-2117080803/10000000000 : ℝ)*X 1 1+(610774827/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2728721167/5000000000 : ℝ)*X 2 0+(977239731/2000000000 : ℝ)*X 2 1+(-423416177/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((20571113/50000000 : ℝ)*X 0 0+(307292249/1000000000 : ℝ)*X 0 1+(2705942109/5000000000 : ℝ)*X 0 2+(20571113/50000000 : ℝ)*X 1 0+(307292249/1000000000 : ℝ)*X 1 1+(2705942109/5000000000 : ℝ)*X 1 2+(20571113/50000000 : ℝ)*X 2 0+(307292249/1000000000 : ℝ)*X 2 1+(2705942109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-317119231/2000000000 : ℝ)*X 0 0+(2455340881/5000000000 : ℝ)*X 0 1+(5824072333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1038870897/2000000000 : ℝ)*X 1 0+(-147400821/1250000000 : ℝ)*X 1 1+(5824072589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597177277/5000000000 : ℝ)*X 2 0+(1164814471/2000000000 : ℝ)*X 2 1+(-294801707/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((515163711/1250000000 : ℝ)*X 0 0+(5352433627/10000000000 : ℝ)*X 0 1+(3134495841/10000000000 : ℝ)*X 0 2+(515163711/1250000000 : ℝ)*X 1 0+(5352433627/10000000000 : ℝ)*X 1 1+(3134495841/10000000000 : ℝ)*X 1 2+(515163711/1250000000 : ℝ)*X 2 0+(5352433627/10000000000 : ℝ)*X 2 1+(3134495841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148205697808799523839757/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11143497/25000000000000 : ℝ)*(base1) + (1149302993/100000000000000 : ℝ)*(base19) + (1130279801/100000000000000 : ℝ)*(base23) + (82289653/50000000000000 : ℝ)*(upper3) + (134213277/100000000000000 : ℝ)*(upper5) + (732862383257689/100000000000000 : ℝ)*(major0) + (732862383257689/100000000000000 : ℝ)*(major1) + (73286238325769/10000000000000 : ℝ)*(major2) + (519088380295871/50000000000000 : ℝ)*(sp0) + (259544921726577/25000000000000 : ℝ)*(sp1) + (2076359411859/200000000000 : ℝ)*(sp2) + (17101672896807/4000000000000 : ℝ)*(sp3) + (4120191547/100000000000000 : ℝ)*(sp4) + (233213039/12500000000000 : ℝ)*(sp7) + (17101749307939/4000000000000 : ℝ)*(f.failure) + (1038180836209301/100000000000000 : ℝ)*(f.sum) + (794204936122809/400000000000000000000000000000 : ℝ)*base65 + (272585579450501/40000000000000000000000000000 : ℝ)*base68 + (4692914018627819/400000000000000000000000000000 : ℝ)*base69 + (126739290501/40000000000000000000000000000 : ℝ)*base72 + (908454617877191/400000000000000000000000000000 : ℝ)*base74 + (3372329755827819/400000000000000000000000000000 : ℝ)*base75 + (1896089598572181/400000000000000000000000000000 : ℝ)*base78 + (819760314227819/400000000000000000000000000000 : ℝ)*base79 + (1511772055427819/200000000000000000000000000000 : ℝ)*base81 + (1274009/200000000000000000000 : ℝ)*base89 + (1274009/200000000000000000000 : ℝ)*base91 + (725991/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (839300093902692306569439/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (899027023/100000000000000 : ℝ)*(base19) + (462371261/50000000000000 : ℝ)*(base23) + (71392291/50000000000000 : ℝ)*(base32) + (34718467/20000000000000 : ℝ)*(upper3) + (18721827/50000000000000 : ℝ)*(upper5) + (772845058749101/100000000000000 : ℝ)*(major0) + (772845058749101/100000000000000 : ℝ)*(major1) + (772845058749101/100000000000000 : ℝ)*(major2) + (1225443091/50000000000000 : ℝ)*(sp1) + (2671471343/100000000000000 : ℝ)*(sp2) + (547410399201139/50000000000000 : ℝ)*(sp4) + (68426090530567/6250000000000 : ℝ)*(sp5) + (1094817202188413/100000000000000 : ℝ)*(sp6) + (450869036427989/100000000000000 : ℝ)*(sp7) + (450869179212571/100000000000000 : ℝ)*(f.failure) + (547410399201139/50000000000000 : ℝ)*(f.sum) + (57358518136729/200000000000000000000000000000 : ℝ)*base66 + (1929931225336729/400000000000000000000000000000 : ℝ)*base68 + (1657542578936729/400000000000000000000000000000 : ℝ)*base70 + (1051527814263271/400000000000000000000000000000 : ℝ)*base71 + (221114661936729/200000000000000000000000000000 : ℝ)*base74 + (161221357336729/400000000000000000000000000000 : ℝ)*base76 + (956825168136729/400000000000000000000000000000 : ℝ)*base78 + (1681296202936729/400000000000000000000000000000 : ℝ)*base80 + (555878504263271/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (36972801/5000000000000000000000 : ℝ)*base89 + (36972801/5000000000000000000000 : ℝ)*base91 + (36972801/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1601_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (239/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24451/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1601_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1601_s1_0 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85515243/500000000 : ℝ)*x 0 + (1384639441/2500000000 : ℝ)*x 1 + (5114613691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85515243/500000000 : ℝ)^4723 ≤ (5244862059189/50000000000000 : ℝ)^3699 := by
    have hnat : (85515243 : ℕ)^4723*50000000000000^3699 ≤ 5244862059189^3699*500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85515243 500000000 5244862059189 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384639441/2500000000 : ℝ)^4723 ≤ (4702846358701/10000000000000 : ℝ)^3699 := by
    have hnat : (1384639441 : ℕ)^4723*10000000000000^3699 ≤ 4702846358701^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384639441 2500000000 4702846358701 10000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5114613691/10000000000 : ℝ)^4723 ≤ (21240906139253/50000000000000 : ℝ)^3699 := by
    have hnat : (5114613691 : ℕ)^4723*50000000000000^3699 ≤ 21240906139253^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114613691 10000000000 21240906139253 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85515243/500000000 : ℝ), (1384639441/2500000000 : ℝ), (5114613691/10000000000 : ℝ)] ![(5244862059189/50000000000000 : ℝ), (4702846358701/10000000000000 : ℝ), (21240906139253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85515243/500000000 : ℝ)|^4723 ≤ (5244862059189/50000000000000 : ℝ)^3699
        have hw : |(-85515243/500000000 : ℝ)|=(85515243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1384639441/2500000000 : ℝ)|^4723 ≤ (4702846358701/10000000000000 : ℝ)^3699
        have hw : |(1384639441/2500000000 : ℝ)|=(1384639441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5114613691/10000000000 : ℝ)|^4723 ≤ (21240906139253/50000000000000 : ℝ)^3699
        have hw : |(5114613691/10000000000 : ℝ)|=(5114613691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s1_1 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074937027/2000000000 : ℝ)*x 0 + (-96618413/500000000 : ℝ)*x 1 + (5114613547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074937027/2000000000 : ℝ)^4723 ≤ (45259133038369/100000000000000 : ℝ)^3699 := by
    have hnat : (1074937027 : ℕ)^4723*100000000000000^3699 ≤ 45259133038369^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074937027 2000000000 45259133038369 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96618413/500000000 : ℝ)^4723 ≤ (383095506187/3125000000000 : ℝ)^3699 := by
    have hnat : (96618413 : ℕ)^4723*3125000000000^3699 ≤ 383095506187^3699*500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96618413 500000000 383095506187 3125000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5114613547/10000000000 : ℝ)^4723 ≤ (2124090537567/5000000000000 : ℝ)^3699 := by
    have hnat : (5114613547 : ℕ)^4723*5000000000000^3699 ≤ 2124090537567^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114613547 10000000000 2124090537567 5000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074937027/2000000000 : ℝ), (-96618413/500000000 : ℝ), (5114613547/10000000000 : ℝ)] ![(45259133038369/100000000000000 : ℝ), (383095506187/3125000000000 : ℝ), (2124090537567/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074937027/2000000000 : ℝ)|^4723 ≤ (45259133038369/100000000000000 : ℝ)^3699
        have hw : |(1074937027/2000000000 : ℝ)|=(1074937027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96618413/500000000 : ℝ)|^4723 ≤ (383095506187/3125000000000 : ℝ)^3699
        have hw : |(-96618413/500000000 : ℝ)|=(96618413/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5114613547/10000000000 : ℝ)|^4723 ≤ (2124090537567/5000000000000 : ℝ)^3699
        have hw : |(5114613547/10000000000 : ℝ)|=(5114613547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s1_2 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687342379/5000000000 : ℝ)*x 0 + (5114613873/10000000000 : ℝ)*x 1 + (-966184167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687342379/5000000000 : ℝ)^4723 ≤ (5657391123111/12500000000000 : ℝ)^3699 := by
    have hnat : (2687342379 : ℕ)^4723*12500000000000^3699 ≤ 5657391123111^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687342379 5000000000 5657391123111 12500000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5114613873/10000000000 : ℝ)^4723 ≤ (21240907104337/50000000000000 : ℝ)^3699 := by
    have hnat : (5114613873 : ℕ)^4723*50000000000000^3699 ≤ 21240907104337^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114613873 10000000000 21240907104337 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966184167/5000000000 : ℝ)^4723 ≤ (6129528398703/50000000000000 : ℝ)^3699 := by
    have hnat : (966184167 : ℕ)^4723*50000000000000^3699 ≤ 6129528398703^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966184167 5000000000 6129528398703 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687342379/5000000000 : ℝ), (5114613873/10000000000 : ℝ), (-966184167/5000000000 : ℝ)] ![(5657391123111/12500000000000 : ℝ), (21240907104337/50000000000000 : ℝ), (6129528398703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687342379/5000000000 : ℝ)|^4723 ≤ (5657391123111/12500000000000 : ℝ)^3699
        have hw : |(2687342379/5000000000 : ℝ)|=(2687342379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5114613873/10000000000 : ℝ)|^4723 ≤ (21240907104337/50000000000000 : ℝ)^3699
        have hw : |(5114613873/10000000000 : ℝ)|=(5114613873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966184167/5000000000 : ℝ)|^4723 ≤ (6129528398703/50000000000000 : ℝ)^3699
        have hw : |(-966184167/5000000000 : ℝ)|=(966184167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s1_3 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2103856221/5000000000 : ℝ)*x 0 + (3717497481/10000000000 : ℝ)*x 1 + (1186734429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103856221/5000000000 : ℝ)^4723 ≤ (2069427164539/6250000000000 : ℝ)^3699 := by
    have hnat : (2103856221 : ℕ)^4723*6250000000000^3699 ≤ 2069427164539^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103856221 5000000000 2069427164539 6250000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3717497481/10000000000 : ℝ)^4723 ≤ (1413359057663/5000000000000 : ℝ)^3699 := by
    have hnat : (3717497481 : ℕ)^4723*5000000000000^3699 ≤ 1413359057663^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717497481 10000000000 1413359057663 5000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1186734429/2500000000 : ℝ)^4723 ≤ (38621984203433/100000000000000 : ℝ)^3699 := by
    have hnat : (1186734429 : ℕ)^4723*100000000000000^3699 ≤ 38621984203433^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186734429 2500000000 38621984203433 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103856221/5000000000 : ℝ), (3717497481/10000000000 : ℝ), (1186734429/2500000000 : ℝ)] ![(2069427164539/6250000000000 : ℝ), (1413359057663/5000000000000 : ℝ), (38621984203433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103856221/5000000000 : ℝ)|^4723 ≤ (2069427164539/6250000000000 : ℝ)^3699
        have hw : |(2103856221/5000000000 : ℝ)|=(2103856221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3717497481/10000000000 : ℝ)|^4723 ≤ (1413359057663/5000000000000 : ℝ)^3699
        have hw : |(3717497481/10000000000 : ℝ)|=(3717497481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1186734429/2500000000 : ℝ)|^4723 ≤ (38621984203433/100000000000000 : ℝ)^3699
        have hw : |(1186734429/2500000000 : ℝ)|=(1186734429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s1_4 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68421903/400000000 : ℝ)*x 0 + (2559654103/5000000000 : ℝ)*x 1 + (2766894567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68421903/400000000 : ℝ)^4723 ≤ (10491624887193/100000000000000 : ℝ)^3699 := by
    have hnat : (68421903 : ℕ)^4723*100000000000000^3699 ≤ 10491624887193^3699*400000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68421903 400000000 10491624887193 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559654103/5000000000 : ℝ)^4723 ≤ (21265802720137/50000000000000 : ℝ)^3699 := by
    have hnat : (2559654103 : ℕ)^4723*50000000000000^3699 ≤ 21265802720137^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559654103 5000000000 21265802720137 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2766894567/5000000000 : ℝ)^4723 ≤ (23488384827251/50000000000000 : ℝ)^3699 := by
    have hnat : (2766894567 : ℕ)^4723*50000000000000^3699 ≤ 23488384827251^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766894567 5000000000 23488384827251 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68421903/400000000 : ℝ), (2559654103/5000000000 : ℝ), (2766894567/5000000000 : ℝ)] ![(10491624887193/100000000000000 : ℝ), (21265802720137/50000000000000 : ℝ), (23488384827251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68421903/400000000 : ℝ)|^4723 ≤ (10491624887193/100000000000000 : ℝ)^3699
        have hw : |(-68421903/400000000 : ℝ)|=(68421903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559654103/5000000000 : ℝ)|^4723 ≤ (21265802720137/50000000000000 : ℝ)^3699
        have hw : |(2559654103/5000000000 : ℝ)|=(2559654103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2766894567/5000000000 : ℝ)|^4723 ≤ (23488384827251/50000000000000 : ℝ)^3699
        have hw : |(2766894567/5000000000 : ℝ)|=(2766894567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s1_5 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328879011/625000000 : ℝ)*x 0 + (-1513192591/10000000000 : ℝ)*x 1 + (221351577/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328879011/625000000 : ℝ)^4723 ≤ (8810353842669/20000000000000 : ℝ)^3699 := by
    have hnat : (328879011 : ℕ)^4723*20000000000000^3699 ≤ 8810353842669^3699*625000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328879011 625000000 8810353842669 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1513192591/10000000000 : ℝ)^4723 ≤ (2242864491833/25000000000000 : ℝ)^3699 := by
    have hnat : (1513192591 : ℕ)^4723*25000000000000^3699 ≤ 2242864491833^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513192591 10000000000 2242864491833 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221351577/400000000 : ℝ)^4723 ≤ (46976772808687/100000000000000 : ℝ)^3699 := by
    have hnat : (221351577 : ℕ)^4723*100000000000000^3699 ≤ 46976772808687^3699*400000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221351577 400000000 46976772808687 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328879011/625000000 : ℝ), (-1513192591/10000000000 : ℝ), (221351577/400000000 : ℝ)] ![(8810353842669/20000000000000 : ℝ), (2242864491833/25000000000000 : ℝ), (46976772808687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328879011/625000000 : ℝ)|^4723 ≤ (8810353842669/20000000000000 : ℝ)^3699
        have hw : |(328879011/625000000 : ℝ)|=(328879011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1513192591/10000000000 : ℝ)|^4723 ≤ (2242864491833/25000000000000 : ℝ)^3699
        have hw : |(-1513192591/10000000000 : ℝ)|=(1513192591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221351577/400000000 : ℝ)|^4723 ≤ (46976772808687/100000000000000 : ℝ)^3699
        have hw : |(221351577/400000000 : ℝ)|=(221351577/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s1_6 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315515903/2500000000 : ℝ)*x 0 + (2766894817/5000000000 : ℝ)*x 1 + (-11821821/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315515903/2500000000 : ℝ)^4723 ≤ (44051763184697/100000000000000 : ℝ)^3699 := by
    have hnat : (1315515903 : ℕ)^4723*100000000000000^3699 ≤ 44051763184697^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315515903 2500000000 44051763184697 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2766894817/5000000000 : ℝ)^4723 ≤ (2936048442129/6250000000000 : ℝ)^3699 := by
    have hnat : (2766894817 : ℕ)^4723*6250000000000^3699 ≤ 2936048442129^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766894817 5000000000 2936048442129 6250000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11821821/78125000 : ℝ)^4723 ≤ (8971461729679/100000000000000 : ℝ)^3699 := by
    have hnat : (11821821 : ℕ)^4723*100000000000000^3699 ≤ 8971461729679^3699*78125000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11821821 78125000 8971461729679 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315515903/2500000000 : ℝ), (2766894817/5000000000 : ℝ), (-11821821/78125000 : ℝ)] ![(44051763184697/100000000000000 : ℝ), (2936048442129/6250000000000 : ℝ), (8971461729679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315515903/2500000000 : ℝ)|^4723 ≤ (44051763184697/100000000000000 : ℝ)^3699
        have hw : |(1315515903/2500000000 : ℝ)|=(1315515903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2766894817/5000000000 : ℝ)|^4723 ≤ (2936048442129/6250000000000 : ℝ)^3699
        have hw : |(2766894817/5000000000 : ℝ)|=(2766894817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11821821/78125000 : ℝ)|^4723 ≤ (8971461729679/100000000000000 : ℝ)^3699
        have hw : |(-11821821/78125000 : ℝ)|=(11821821/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s1_7 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208300979/10000000000 : ℝ)*x 0 + (591942399/1250000000 : ℝ)*x 1 + (372907593/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208300979/10000000000 : ℝ)^4723 ≤ (33116748068193/100000000000000 : ℝ)^3699 := by
    have hnat : (4208300979 : ℕ)^4723*100000000000000^3699 ≤ 33116748068193^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208300979 10000000000 33116748068193 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591942399/1250000000 : ℝ)^4723 ≤ (38503609520991/100000000000000 : ℝ)^3699 := by
    have hnat : (591942399 : ℕ)^4723*100000000000000^3699 ≤ 38503609520991^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591942399 1250000000 38503609520991 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372907593/1000000000 : ℝ)^4723 ≤ (28379642393161/100000000000000 : ℝ)^3699 := by
    have hnat : (372907593 : ℕ)^4723*100000000000000^3699 ≤ 28379642393161^3699*1000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372907593 1000000000 28379642393161 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208300979/10000000000 : ℝ), (591942399/1250000000 : ℝ), (372907593/1000000000 : ℝ)] ![(33116748068193/100000000000000 : ℝ), (38503609520991/100000000000000 : ℝ), (28379642393161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208300979/10000000000 : ℝ)|^4723 ≤ (33116748068193/100000000000000 : ℝ)^3699
        have hw : |(4208300979/10000000000 : ℝ)|=(4208300979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(591942399/1250000000 : ℝ)|^4723 ≤ (38503609520991/100000000000000 : ℝ)^3699
        have hw : |(591942399/1250000000 : ℝ)|=(591942399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(372907593/1000000000 : ℝ)|^4723 ≤ (28379642393161/100000000000000 : ℝ)^3699
        have hw : |(372907593/1000000000 : ℝ)|=(372907593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1601_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24451/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2241/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2243/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24451/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (239/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24451/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (239/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24451/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (239/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24451/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (239/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24451/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (239/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24451/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (239/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (239/6250 : ℝ) ^ (4719/1024 : ℝ) ≤ (29354698870917/100000000000000000000 : ℝ) := by
    have hpowers : (239/6250 : ℝ)^4719 ≤ (29354698870917/100000000000000000000 : ℝ)^1024 := by
      have hnat : (239 : ℕ)^4719*100000000000000000000^1024 ≤ 29354698870917^1024*6250^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        239 6250 29354698870917 100000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (239/6250 : ℝ)) (X := (29354698870917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24451/100000 : ℝ) ^ (4719/1024 : ℝ) ≤ (7585725616572189/5000000000000000000 : ℝ) := by
    have hpowers : (24451/100000 : ℝ)^4719 ≤ (7585725616572189/5000000000000000000 : ℝ)^1024 := by
      have hnat : (24451 : ℕ)^4719*5000000000000000000^1024 ≤ 7585725616572189^1024*100000^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24451 100000 7585725616572189 5000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24451/100000 : ℝ)) (X := (7585725616572189/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000029354698870917/50000000000000000000 : ℝ) ≤ (312500039811407/312500000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (50000029354698870917/50000000000000000000 : ℝ)^1024 ≤ (312500039811407/312500000000000 : ℝ)^4719 := by
      have hnat : (50000029354698870917 : ℕ)^1024*312500000000000^4719 ≤ 312500039811407^4719*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000029354698870917 50000000000000000000 312500039811407 312500000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500039811407/312500000000000 : ℝ)) (X := (50000029354698870917/50000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100151743867030314697/100000000000000000000 : ℝ) ≤ (5001645406773787/5000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (100151743867030314697/100000000000000000000 : ℝ)^1024 ≤ (5001645406773787/5000000000000000 : ℝ)^4719 := by
      have hnat : (100151743867030314697 : ℕ)^1024*5000000000000000^4719 ≤ 5001645406773787^4719*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100151743867030314697 100000000000000000000 5001645406773787 5000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001645406773787/5000000000000000 : ℝ)) (X := (100151743867030314697/100000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2507585725616572189/2500000000000000000 : ℝ) ≤ (2501645088282531/2500000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (2507585725616572189/2500000000000000000 : ℝ)^1024 ≤ (2501645088282531/2500000000000000 : ℝ)^4719 := by
      have hnat : (2507585725616572189 : ℕ)^1024*2500000000000000^4719 ≤ 2501645088282531^4719*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2507585725616572189 2500000000000000000 2501645088282531 2500000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501645088282531/2500000000000000 : ℝ)) (X := (2507585725616572189/2500000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29354698870917/100000000000000000000 : ℝ) ≤ ((6445152121229662739/6445937500000000000 : ℝ)+2*(65790791651/41254000000000 : ℝ)*(239/6250 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (6445152121229662739/6445937500000000000 : ℝ)+2*(65790791651/41254000000000 : ℝ)*(239/6250 : ℝ)=(312500039811407/312500000000000 : ℝ) by norm_num, show 1+2*(29354698870917/100000000000000000000 : ℝ)=(50000029354698870917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7585725616572189/5000000000000000000 : ℝ)+(29354698870917/100000000000000000000 : ℝ) ≤ ((6445152121229662739/6445937500000000000 : ℝ)+(65790791651/41254000000000 : ℝ)*((24451/100000 : ℝ)+(239/6250 : ℝ)))^(4719/1024 : ℝ) := by
    rw [show (6445152121229662739/6445937500000000000 : ℝ)+(65790791651/41254000000000 : ℝ)*((24451/100000 : ℝ)+(239/6250 : ℝ))=(5001645406773787/5000000000000000 : ℝ) by norm_num, show 1+(7585725616572189/5000000000000000000 : ℝ)+(29354698870917/100000000000000000000 : ℝ)=(100151743867030314697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7585725616572189/5000000000000000000 : ℝ) ≤ ((6445152121229662739/6445937500000000000 : ℝ)+2*(65790791651/41254000000000 : ℝ)*(24451/100000 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (6445152121229662739/6445937500000000000 : ℝ)+2*(65790791651/41254000000000 : ℝ)*(24451/100000 : ℝ)=(2501645088282531/2500000000000000 : ℝ) by norm_num, show 1+2*(7585725616572189/5000000000000000000 : ℝ)=(2507585725616572189/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6445152121229662739/6445937500000000000 : ℝ)*(X 1 0+X 2 0)+(65790791651/41254000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (239/6250 : ℝ)) (hi := (24451/100000 : ℝ)) (c := (6445152121229662739/6445937500000000000 : ℝ)) (alpha := (65790791651/41254000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6445152121229662739/6445937500000000000 : ℝ)*(X 0 1+X 2 1)+(65790791651/41254000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (239/6250 : ℝ)) (hi := (24451/100000 : ℝ)) (c := (6445152121229662739/6445937500000000000 : ℝ)) (alpha := (65790791651/41254000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6445152121229662739/6445937500000000000 : ℝ)*(X 0 2+X 1 2)+(65790791651/41254000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (239/6250 : ℝ)) (hi := (24451/100000 : ℝ)) (c := (6445152121229662739/6445937500000000000 : ℝ)) (alpha := (65790791651/41254000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85515243/500000000 : ℝ)*X 0 0+(1384639441/2500000000 : ℝ)*X 0 1+(5114613691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074937027/2000000000 : ℝ)*X 1 0+(-96618413/500000000 : ℝ)*X 1 1+(5114613547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687342379/5000000000 : ℝ)*X 2 0+(5114613873/10000000000 : ℝ)*X 2 1+(-966184167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2103856221/5000000000 : ℝ)*X 0 0+(3717497481/10000000000 : ℝ)*X 0 1+(1186734429/2500000000 : ℝ)*X 0 2+(2103856221/5000000000 : ℝ)*X 1 0+(3717497481/10000000000 : ℝ)*X 1 1+(1186734429/2500000000 : ℝ)*X 1 2+(2103856221/5000000000 : ℝ)*X 2 0+(3717497481/10000000000 : ℝ)*X 2 1+(1186734429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68421903/400000000 : ℝ)*X 0 0+(2559654103/5000000000 : ℝ)*X 0 1+(2766894567/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328879011/625000000 : ℝ)*X 1 0+(-1513192591/10000000000 : ℝ)*X 1 1+(221351577/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315515903/2500000000 : ℝ)*X 2 0+(2766894817/5000000000 : ℝ)*X 2 1+(-11821821/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208300979/10000000000 : ℝ)*X 0 0+(591942399/1250000000 : ℝ)*X 0 1+(372907593/1000000000 : ℝ)*X 0 2+(4208300979/10000000000 : ℝ)*X 1 0+(591942399/1250000000 : ℝ)*X 1 1+(372907593/1000000000 : ℝ)*X 1 2+(4208300979/10000000000 : ℝ)*X 2 0+(591942399/1250000000 : ℝ)*X 2 1+(372907593/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3343343028616808200745481939/322296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21814833/20000000000000 : ℝ)*(base1) + (2154104977/100000000000000 : ℝ)*(base19) + (1988647769/100000000000000 : ℝ)*(base23) + (268015177/100000000000000 : ℝ)*(upper3) + (98691403/50000000000000 : ℝ)*(upper5) + (1665126140990679/100000000000000 : ℝ)*(major0) + (1665126140990679/100000000000000 : ℝ)*(major1) + (1665126140990679/100000000000000 : ℝ)*(major2) + (2358819473647207/100000000000000 : ℝ)*(sp0) + (589708445237383/25000000000000 : ℝ)*(sp1) + (2358833946406739/100000000000000 : ℝ)*(sp2) + (971408614582967/100000000000000 : ℝ)*(sp3) + (16570481467/100000000000000 : ℝ)*(sp4) + (7277486753/100000000000000 : ℝ)*(sp7) + (194283200228777/20000000000000 : ℝ)*(f.failure) + (589708983763627/25000000000000 : ℝ)*(f.sum) + (1574865989589/10313500000000000000000000000 : ℝ)*base65 + (1426443517916172281/644593750000000000000000000000000 : ℝ)*base67 + (1123667375652172281/644593750000000000000000000000000 : ℝ)*base69 + (1418664613044327719/644593750000000000000000000000000 : ℝ)*base72 + (17549702085149/20627000000000000000000000000 : ℝ)*base73 + (458820883873953531/644593750000000000000000000000000 : ℝ)*base75 + (2999266635910859781/644593750000000000000000000000000 : ℝ)*base77 + (6145316602237453531/644593750000000000000000000000000 : ℝ)*base79 + (7123036210559/10313500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1531787/1000000000000000000000 : ℝ)*base89 + (1531787/1000000000000000000000 : ℝ)*base91 + (1531787/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1359653695575302711628916011/161148437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (830385067/50000000000000 : ℝ)*(base19) + (1433957883/100000000000000 : ℝ)*(base23) + (5860601/20000000000000 : ℝ)*(upper2) + (289276013/100000000000000 : ℝ)*(upper3) + (132258749/100000000000000 : ℝ)*(upper5) + (851557893413333/50000000000000 : ℝ)*(major0) + (851557893413333/50000000000000 : ℝ)*(major1) + (851557893413333/50000000000000 : ℝ)*(major2) + (3117230247/25000000000000 : ℝ)*(sp1) + (11351921391/100000000000000 : ℝ)*(sp2) + (603163139000897/25000000000000 : ℝ)*(sp4) + (1206319213156233/50000000000000 : ℝ)*(sp5) + (1206319885062157/50000000000000 : ℝ)*(sp6) + (993578736407239/100000000000000 : ℝ)*(sp7) + (993578736407239/100000000000000 : ℝ)*(f.failure) + (603163139000897/25000000000000 : ℝ)*(f.sum) + (59242393734273/20627000000000000000000000000 : ℝ)*base65 + (618530805262257163/322296875000000000000000000000000 : ℝ)*base68 + (919271190900413413/322296875000000000000000000000000 : ℝ)*base70 + (370705558680714519/161148437500000000000000000000000 : ℝ)*base72 + (3527864085897/10313500000000000000000000000 : ℝ)*base74 + (352356384784930337/322296875000000000000000000000000 : ℝ)*base75 + (115858182991833089/40287109375000000000000000000000 : ℝ)*base77 + (211419419782193197/80574218750000000000000000000000 : ℝ)*base80 + (711539704577/322296875000000000000000000 : ℝ)*base82 + (4917691/5000000000000000000000 : ℝ)*base90 + (4917691/5000000000000000000000 : ℝ)*base92 + (4917691/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1601_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24451/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2243/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1601_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1601_s2_0 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1725498189/10000000000 : ℝ)*x 0 + (1367678469/2500000000 : ℝ)*x 1 + (206901143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1725498189/10000000000 : ℝ)^4723 ≤ (5304425481311/50000000000000 : ℝ)^3699 := by
    have hnat : (1725498189 : ℕ)^4723*50000000000000^3699 ≤ 5304425481311^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725498189 10000000000 5304425481311 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367678469/2500000000 : ℝ)^4723 ≤ (23147085384949/50000000000000 : ℝ)^3699 := by
    have hnat : (1367678469 : ℕ)^4723*50000000000000^3699 ≤ 23147085384949^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367678469 2500000000 23147085384949 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206901143/400000000 : ℝ)^4723 ≤ (21548489130313/50000000000000 : ℝ)^3699 := by
    have hnat : (206901143 : ℕ)^4723*50000000000000^3699 ≤ 21548489130313^3699*400000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206901143 400000000 21548489130313 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1725498189/10000000000 : ℝ), (1367678469/2500000000 : ℝ), (206901143/400000000 : ℝ)] ![(5304425481311/50000000000000 : ℝ), (23147085384949/50000000000000 : ℝ), (21548489130313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1725498189/10000000000 : ℝ)|^4723 ≤ (5304425481311/50000000000000 : ℝ)^3699
        have hw : |(-1725498189/10000000000 : ℝ)|=(1725498189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367678469/2500000000 : ℝ)|^4723 ≤ (23147085384949/50000000000000 : ℝ)^3699
        have hw : |(1367678469/2500000000 : ℝ)|=(1367678469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206901143/400000000 : ℝ)|^4723 ≤ (21548489130313/50000000000000 : ℝ)^3699
        have hw : |(206901143/400000000 : ℝ)|=(206901143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s2_1 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267853879/500000000 : ℝ)*x 0 + (-601467/3200000 : ℝ)*x 1 + (1293132133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267853879/500000000 : ℝ)^4723 ≤ (2253495179157/5000000000000 : ℝ)^3699 := by
    have hnat : (267853879 : ℕ)^4723*5000000000000^3699 ≤ 2253495179157^3699*500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267853879 500000000 2253495179157 5000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601467/3200000 : ℝ)^4723 ≤ (11833118596823/100000000000000 : ℝ)^3699 := by
    have hnat : (601467 : ℕ)^4723*100000000000000^3699 ≤ 11833118596823^3699*3200000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601467 3200000 11833118596823 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293132133/2500000000 : ℝ)^4723 ≤ (21548488901587/50000000000000 : ℝ)^3699 := by
    have hnat : (1293132133 : ℕ)^4723*50000000000000^3699 ≤ 21548488901587^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293132133 2500000000 21548488901587 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267853879/500000000 : ℝ), (-601467/3200000 : ℝ), (1293132133/2500000000 : ℝ)] ![(2253495179157/5000000000000 : ℝ), (11833118596823/100000000000000 : ℝ), (21548488901587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267853879/500000000 : ℝ)|^4723 ≤ (2253495179157/5000000000000 : ℝ)^3699
        have hw : |(267853879/500000000 : ℝ)|=(267853879/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-601467/3200000 : ℝ)|^4723 ≤ (11833118596823/100000000000000 : ℝ)^3699
        have hw : |(-601467/3200000 : ℝ)|=(601467/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293132133/2500000000 : ℝ)|^4723 ≤ (21548488901587/50000000000000 : ℝ)^3699
        have hw : |(1293132133/2500000000 : ℝ)|=(1293132133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s2_2 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167408669/312500000 : ℝ)*x 0 + (5172528711/10000000000 : ℝ)*x 1 + (-117474023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167408669/312500000 : ℝ)^4723 ≤ (9013980347097/20000000000000 : ℝ)^3699 := by
    have hnat : (167408669 : ℕ)^4723*20000000000000^3699 ≤ 9013980347097^3699*312500000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167408669 312500000 9013980347097 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172528711/10000000000 : ℝ)^4723 ≤ (43096979707453/100000000000000 : ℝ)^3699 := by
    have hnat : (5172528711 : ℕ)^4723*100000000000000^3699 ≤ 43096979707453^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172528711 10000000000 43096979707453 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117474023/625000000 : ℝ)^4723 ≤ (5916559270277/50000000000000 : ℝ)^3699 := by
    have hnat : (117474023 : ℕ)^4723*50000000000000^3699 ≤ 5916559270277^3699*625000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117474023 625000000 5916559270277 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167408669/312500000 : ℝ), (5172528711/10000000000 : ℝ), (-117474023/625000000 : ℝ)] ![(9013980347097/20000000000000 : ℝ), (43096979707453/100000000000000 : ℝ), (5916559270277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167408669/312500000 : ℝ)|^4723 ≤ (9013980347097/20000000000000 : ℝ)^3699
        have hw : |(167408669/312500000 : ℝ)|=(167408669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172528711/10000000000 : ℝ)|^4723 ≤ (43096979707453/100000000000000 : ℝ)^3699
        have hw : |(5172528711/10000000000 : ℝ)|=(5172528711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117474023/625000000 : ℝ)|^4723 ≤ (5916559270277/50000000000000 : ℝ)^3699
        have hw : |(-117474023/625000000 : ℝ)|=(117474023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s2_3 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2109447597/5000000000 : ℝ)*x 0 + (3868987023/10000000000 : ℝ)*x 1 + (4593054059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109447597/5000000000 : ℝ)^4723 ≤ (33223234555719/100000000000000 : ℝ)^3699 := by
    have hnat : (2109447597 : ℕ)^4723*100000000000000^3699 ≤ 33223234555719^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109447597 5000000000 33223234555719 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3868987023/10000000000 : ℝ)^4723 ≤ (14873089128461/50000000000000 : ℝ)^3699 := by
    have hnat : (3868987023 : ℕ)^4723*50000000000000^3699 ≤ 14873089128461^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3868987023 10000000000 14873089128461 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4593054059/10000000000 : ℝ)^4723 ≤ (9257646792537/25000000000000 : ℝ)^3699 := by
    have hnat : (4593054059 : ℕ)^4723*25000000000000^3699 ≤ 9257646792537^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593054059 10000000000 9257646792537 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109447597/5000000000 : ℝ), (3868987023/10000000000 : ℝ), (4593054059/10000000000 : ℝ)] ![(33223234555719/100000000000000 : ℝ), (14873089128461/50000000000000 : ℝ), (9257646792537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109447597/5000000000 : ℝ)|^4723 ≤ (33223234555719/100000000000000 : ℝ)^3699
        have hw : |(2109447597/5000000000 : ℝ)|=(2109447597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3868987023/10000000000 : ℝ)|^4723 ≤ (14873089128461/50000000000000 : ℝ)^3699
        have hw : |(3868987023/10000000000 : ℝ)|=(3868987023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4593054059/10000000000 : ℝ)|^4723 ≤ (9257646792537/25000000000000 : ℝ)^3699
        have hw : |(4593054059/10000000000 : ℝ)|=(4593054059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s2_4 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215697807/1250000000 : ℝ)*x 0 + (5174859101/10000000000 : ℝ)*x 1 + (5468357721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215697807/1250000000 : ℝ)^4723 ≤ (10609512490153/100000000000000 : ℝ)^3699 := by
    have hnat : (215697807 : ℕ)^4723*100000000000000^3699 ≤ 10609512490153^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215697807 1250000000 10609512490153 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174859101/10000000000 : ℝ)^4723 ≤ (269511080901/625000000000 : ℝ)^3699 := by
    have hnat : (5174859101 : ℕ)^4723*625000000000^3699 ≤ 269511080901^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174859101 10000000000 269511080901 625000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468357721/10000000000 : ℝ)^4723 ≤ (46268714551627/100000000000000 : ℝ)^3699 := by
    have hnat : (5468357721 : ℕ)^4723*100000000000000^3699 ≤ 46268714551627^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468357721 10000000000 46268714551627 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215697807/1250000000 : ℝ), (5174859101/10000000000 : ℝ), (5468357721/10000000000 : ℝ)] ![(10609512490153/100000000000000 : ℝ), (269511080901/625000000000 : ℝ), (46268714551627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215697807/1250000000 : ℝ)|^4723 ≤ (10609512490153/100000000000000 : ℝ)^3699
        have hw : |(-215697807/1250000000 : ℝ)|=(215697807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174859101/10000000000 : ℝ)|^4723 ≤ (269511080901/625000000000 : ℝ)^3699
        have hw : |(5174859101/10000000000 : ℝ)|=(5174859101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468357721/10000000000 : ℝ)|^4723 ≤ (46268714551627/100000000000000 : ℝ)^3699
        have hw : |(5468357721/10000000000 : ℝ)|=(5468357721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s2_5 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319501801/2500000000 : ℝ)*x 0 + (-1583755029/10000000000 : ℝ)*x 1 + (2734178621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319501801/2500000000 : ℝ)^4723 ≤ (22111128563927/50000000000000 : ℝ)^3699 := by
    have hnat : (1319501801 : ℕ)^4723*50000000000000^3699 ≤ 22111128563927^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319501801 2500000000 22111128563927 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1583755029/10000000000 : ℝ)^4723 ≤ (9509033480707/100000000000000 : ℝ)^3699 := by
    have hnat : (1583755029 : ℕ)^4723*100000000000000^3699 ≤ 9509033480707^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583755029 10000000000 9509033480707 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734178621/5000000000 : ℝ)^4723 ≤ (23134354688377/50000000000000 : ℝ)^3699 := by
    have hnat : (2734178621 : ℕ)^4723*50000000000000^3699 ≤ 23134354688377^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734178621 5000000000 23134354688377 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319501801/2500000000 : ℝ), (-1583755029/10000000000 : ℝ), (2734178621/5000000000 : ℝ)] ![(22111128563927/50000000000000 : ℝ), (9509033480707/100000000000000 : ℝ), (23134354688377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319501801/2500000000 : ℝ)|^4723 ≤ (22111128563927/50000000000000 : ℝ)^3699
        have hw : |(1319501801/2500000000 : ℝ)|=(1319501801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1583755029/10000000000 : ℝ)|^4723 ≤ (9509033480707/100000000000000 : ℝ)^3699
        have hw : |(-1583755029/10000000000 : ℝ)|=(1583755029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734178621/5000000000 : ℝ)|^4723 ≤ (23134354688377/50000000000000 : ℝ)^3699
        have hw : |(2734178621/5000000000 : ℝ)|=(2734178621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s2_6 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278006383/10000000000 : ℝ)*x 0 + (5468358219/10000000000 : ℝ)*x 1 + (-1583754797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278006383/10000000000 : ℝ)^4723 ≤ (44222248344757/100000000000000 : ℝ)^3699 := by
    have hnat : (5278006383 : ℕ)^4723*100000000000000^3699 ≤ 44222248344757^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278006383 10000000000 44222248344757 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468358219/10000000000 : ℝ)^4723 ≤ (9253743986353/20000000000000 : ℝ)^3699 := by
    have hnat : (5468358219 : ℕ)^4723*20000000000000^3699 ≤ 9253743986353^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468358219 10000000000 9253743986353 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583754797/10000000000 : ℝ)^4723 ≤ (4754515851071/50000000000000 : ℝ)^3699 := by
    have hnat : (1583754797 : ℕ)^4723*50000000000000^3699 ≤ 4754515851071^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583754797 10000000000 4754515851071 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278006383/10000000000 : ℝ), (5468358219/10000000000 : ℝ), (-1583754797/10000000000 : ℝ)] ![(44222248344757/100000000000000 : ℝ), (9253743986353/20000000000000 : ℝ), (4754515851071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278006383/10000000000 : ℝ)|^4723 ≤ (44222248344757/100000000000000 : ℝ)^3699
        have hw : |(5278006383/10000000000 : ℝ)|=(5278006383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468358219/10000000000 : ℝ)|^4723 ≤ (9253743986353/20000000000000 : ℝ)^3699
        have hw : |(5468358219/10000000000 : ℝ)|=(5468358219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1583754797/10000000000 : ℝ)|^4723 ≤ (4754515851071/50000000000000 : ℝ)^3699
        have hw : |(-1583754797/10000000000 : ℝ)|=(1583754797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s2_7 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054775289/2500000000 : ℝ)*x 0 + (4587396263/10000000000 : ℝ)*x 1 + (774941371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054775289/2500000000 : ℝ)^4723 ≤ (33225305492421/100000000000000 : ℝ)^3699 := by
    have hnat : (1054775289 : ℕ)^4723*100000000000000^3699 ≤ 33225305492421^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054775289 2500000000 33225305492421 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4587396263/10000000000 : ℝ)^4723 ≤ (1155386081649/3125000000000 : ℝ)^3699 := by
    have hnat : (4587396263 : ℕ)^4723*3125000000000^3699 ≤ 1155386081649^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4587396263 10000000000 1155386081649 3125000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774941371/2000000000 : ℝ)^4723 ≤ (14901169938023/50000000000000 : ℝ)^3699 := by
    have hnat : (774941371 : ℕ)^4723*50000000000000^3699 ≤ 14901169938023^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774941371 2000000000 14901169938023 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054775289/2500000000 : ℝ), (4587396263/10000000000 : ℝ), (774941371/2000000000 : ℝ)] ![(33225305492421/100000000000000 : ℝ), (1155386081649/3125000000000 : ℝ), (14901169938023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054775289/2500000000 : ℝ)|^4723 ≤ (33225305492421/100000000000000 : ℝ)^3699
        have hw : |(1054775289/2500000000 : ℝ)|=(1054775289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4587396263/10000000000 : ℝ)|^4723 ≤ (1155386081649/3125000000000 : ℝ)^3699
        have hw : |(4587396263/10000000000 : ℝ)|=(4587396263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(774941371/2000000000 : ℝ)|^4723 ≤ (14901169938023/50000000000000 : ℝ)^3699
        have hw : |(774941371/2000000000 : ℝ)|=(774941371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1601_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2243/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2043/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16533/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2243/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2241/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2243/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2241/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2243/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2241/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2243/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2241/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2243/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2241/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2243/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2241/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2241/25000 : ℝ) ^ (4719/1024 : ℝ) ≤ (744185419358003/50000000000000000000 : ℝ) := by
    have hpowers : (2241/25000 : ℝ)^4719 ≤ (744185419358003/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2241 : ℕ)^4719*50000000000000000000^1024 ≤ 744185419358003^1024*25000^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2241 25000 744185419358003 50000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2241/25000 : ℝ)) (X := (744185419358003/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2243/12500 : ℝ) ^ (4719/1024 : ℝ) ≤ (9113867173908883/25000000000000000000 : ℝ) := by
    have hpowers : (2243/12500 : ℝ)^4719 ≤ (9113867173908883/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2243 : ℕ)^4719*25000000000000000000^1024 ≤ 9113867173908883^1024*12500^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 12500 9113867173908883 25000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/12500 : ℝ)) (X := (9113867173908883/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000744185419358003/25000000000000000000 : ℝ) ≤ (5000032296545399/5000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (25000744185419358003/25000000000000000000 : ℝ)^1024 ≤ (5000032296545399/5000000000000000 : ℝ)^4719 := by
      have hnat : (25000744185419358003 : ℕ)^1024*5000000000000000^4719 ≤ 5000032296545399^4719*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000744185419358003 25000000000000000000 5000032296545399 5000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000032296545399/5000000000000000 : ℝ)) (X := (25000744185419358003/25000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018971919767175769/50000000000000000000 : ℝ) ≤ (10000823240540553/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (50018971919767175769/50000000000000000000 : ℝ)^1024 ≤ (10000823240540553/10000000000000000 : ℝ)^4719 := by
      have hnat : (50018971919767175769 : ℕ)^1024*10000000000000000^4719 ≤ 10000823240540553^4719*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018971919767175769 50000000000000000000 10000823240540553 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000823240540553/10000000000000000 : ℝ)) (X := (50018971919767175769/50000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509113867173908883/12500000000000000000 : ℝ) ≤ (2500395471997577/2500000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (12509113867173908883/12500000000000000000 : ℝ)^1024 ≤ (2500395471997577/2500000000000000 : ℝ)^4719 := by
      have hnat : (12509113867173908883 : ℕ)^1024*2500000000000000^4719 ≤ 2500395471997577^4719*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509113867173908883 12500000000000000000 2500395471997577 2500000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500395471997577/2500000000000000 : ℝ)) (X := (12509113867173908883/12500000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(744185419358003/50000000000000000000 : ℝ) ≤ ((56116861884047599/56125000000000000 : ℝ)+2*(151729489951/179600000000000 : ℝ)*(2241/25000 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (56116861884047599/56125000000000000 : ℝ)+2*(151729489951/179600000000000 : ℝ)*(2241/25000 : ℝ)=(5000032296545399/5000000000000000 : ℝ) by norm_num, show 1+2*(744185419358003/50000000000000000000 : ℝ)=(25000744185419358003/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9113867173908883/25000000000000000000 : ℝ)+(744185419358003/50000000000000000000 : ℝ) ≤ ((56116861884047599/56125000000000000 : ℝ)+(151729489951/179600000000000 : ℝ)*((2243/12500 : ℝ)+(2241/25000 : ℝ)))^(4719/1024 : ℝ) := by
    rw [show (56116861884047599/56125000000000000 : ℝ)+(151729489951/179600000000000 : ℝ)*((2243/12500 : ℝ)+(2241/25000 : ℝ))=(10000823240540553/10000000000000000 : ℝ) by norm_num, show 1+(9113867173908883/25000000000000000000 : ℝ)+(744185419358003/50000000000000000000 : ℝ)=(50018971919767175769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9113867173908883/25000000000000000000 : ℝ) ≤ ((56116861884047599/56125000000000000 : ℝ)+2*(151729489951/179600000000000 : ℝ)*(2243/12500 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (56116861884047599/56125000000000000 : ℝ)+2*(151729489951/179600000000000 : ℝ)*(2243/12500 : ℝ)=(2500395471997577/2500000000000000 : ℝ) by norm_num, show 1+2*(9113867173908883/25000000000000000000 : ℝ)=(12509113867173908883/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56116861884047599/56125000000000000 : ℝ)*(X 1 0+X 2 0)+(151729489951/179600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (2241/25000 : ℝ)) (hi := (2243/12500 : ℝ)) (c := (56116861884047599/56125000000000000 : ℝ)) (alpha := (151729489951/179600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56116861884047599/56125000000000000 : ℝ)*(X 0 1+X 2 1)+(151729489951/179600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (2241/25000 : ℝ)) (hi := (2243/12500 : ℝ)) (c := (56116861884047599/56125000000000000 : ℝ)) (alpha := (151729489951/179600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56116861884047599/56125000000000000 : ℝ)*(X 0 2+X 1 2)+(151729489951/179600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (2241/25000 : ℝ)) (hi := (2243/12500 : ℝ)) (c := (56116861884047599/56125000000000000 : ℝ)) (alpha := (151729489951/179600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1725498189/10000000000 : ℝ)*X 0 0+(1367678469/2500000000 : ℝ)*X 0 1+(206901143/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267853879/500000000 : ℝ)*X 1 0+(-601467/3200000 : ℝ)*X 1 1+(1293132133/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167408669/312500000 : ℝ)*X 2 0+(5172528711/10000000000 : ℝ)*X 2 1+(-117474023/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2109447597/5000000000 : ℝ)*X 0 0+(3868987023/10000000000 : ℝ)*X 0 1+(4593054059/10000000000 : ℝ)*X 0 2+(2109447597/5000000000 : ℝ)*X 1 0+(3868987023/10000000000 : ℝ)*X 1 1+(4593054059/10000000000 : ℝ)*X 1 2+(2109447597/5000000000 : ℝ)*X 2 0+(3868987023/10000000000 : ℝ)*X 2 1+(4593054059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215697807/1250000000 : ℝ)*X 0 0+(5174859101/10000000000 : ℝ)*X 0 1+(5468357721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319501801/2500000000 : ℝ)*X 1 0+(-1583755029/10000000000 : ℝ)*X 1 1+(2734178621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278006383/10000000000 : ℝ)*X 2 0+(5468358219/10000000000 : ℝ)*X 2 1+(-1583754797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1054775289/2500000000 : ℝ)*X 0 0+(4587396263/10000000000 : ℝ)*X 0 1+(774941371/2000000000 : ℝ)*X 0 2+(1054775289/2500000000 : ℝ)*X 1 0+(4587396263/10000000000 : ℝ)*X 1 1+(774941371/2000000000 : ℝ)*X 1 2+(1054775289/2500000000 : ℝ)*X 2 0+(4587396263/10000000000 : ℝ)*X 2 1+(774941371/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32860760965291726846662411/2806250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (946299199/50000000000000 : ℝ)*(base19) + (417159777/25000000000000 : ℝ)*(base23) + (12458757/20000000000000 : ℝ)*(lower2) + (301099557/100000000000000 : ℝ)*(upper3) + (200864763/100000000000000 : ℝ)*(upper5) + (1183691654273053/50000000000000 : ℝ)*(major0) + (1183691654273053/50000000000000 : ℝ)*(major1) + (1183691654273053/50000000000000 : ℝ)*(major2) + (3353641015449089/100000000000000 : ℝ)*(sp0) + (1676829670743241/50000000000000 : ℝ)*(sp1) + (838414891361443/25000000000000 : ℝ)*(sp2) + (690547901501219/50000000000000 : ℝ)*(sp3) + (1263664737/6250000000000 : ℝ)*(sp4) + (4594838309/50000000000000 : ℝ)*(sp7) + (1381104992679057/100000000000000 : ℝ)*(f.failure) + (41920765426061/1250000000000 : ℝ)*(f.sum) + (38295609642973/4490000000000000000000000000 : ℝ)*base65 + (12007041793651369/5612500000000000000000000000000 : ℝ)*base67 + (5111857029786131/5612500000000000000000000000000 : ℝ)*base70 + (72228693233351369/5612500000000000000000000000000 : ℝ)*base71 + (19833926447983/4490000000000000000000000000 : ℝ)*base73 + (1303588452301369/5612500000000000000000000000000 : ℝ)*base75 + (94482000836051369/5612500000000000000000000000000 : ℝ)*base77 + (70465955377851369/5612500000000000000000000000000 : ℝ)*base79 + (13424010179763/4490000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (198467/5000000000000000000000 : ℝ)*base89 + (198467/5000000000000000000000 : ℝ)*base91 + (198467/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2497841500846165878343137/1403125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288629049/50000000000000 : ℝ)*(base19) + (104839031/20000000000000 : ℝ)*(base23) + (23044653/25000000000000 : ℝ)*(upper3) + (96606701/50000000000000 : ℝ)*(lower4) + (300643975790101/12500000000000 : ℝ)*(major0) + (300643975790101/12500000000000 : ℝ)*(major1) + (300643975790101/12500000000000 : ℝ)*(major2) + (41990097/20000000000000 : ℝ)*(sp1) + (1902347171/25000000000000 : ℝ)*(sp2) + (7403373/400000000000 : ℝ)*(sp3) + (425895605083661/12500000000000 : ℝ)*(sp4) + (106473876670647/3125000000000 : ℝ)*(sp5) + (425894588385681/12500000000000 : ℝ)*(sp6) + (140313686178911/10000000000000 : ℝ)*(sp7) + (35078467815809/2500000000000 : ℝ)*(f.failure) + (425895605083661/12500000000000 : ℝ)*(f.sum) + (3593041247619/1122500000000000000000000000 : ℝ)*base66 + (800004852908127/1403125000000000000000000000000 : ℝ)*base68 + (1541329949216873/1403125000000000000000000000000 : ℝ)*base69 + (18398030132116873/1403125000000000000000000000000 : ℝ)*base71 + (8961760883203/2245000000000000000000000000 : ℝ)*base74 + (18113902860970627/1403125000000000000000000000000 : ℝ)*base76 + (3425104021929373/1403125000000000000000000000000 : ℝ)*base77 + (4368247043179373/1403125000000000000000000000000 : ℝ)*base79 + (5842160901631/1122500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (24979/125000000000000000000 : ℝ)*base89 + (24979/125000000000000000000 : ℝ)*base91 + (24979/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1601_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2243/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2043/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16533/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1601_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1601_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2043/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16533/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1601_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1601_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1601_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2043/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16533/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1601_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
