-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1180_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:17.568993+00:00
-- url     : https://prove2.me/submissions/f677cd4b-85c9-4f45-8c4d-32d4492cf762

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
theorem support_rectangle_w1180_s0_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879841889/10000000000 : ℝ)*x 0 + (1209117797/2000000000 : ℝ)*x 1 + (2392629687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879841889/10000000000 : ℝ)^8373 ≤ (10941725719113/100000000000000 : ℝ)^6325 := by
    have hnat : (1879841889 : ℕ)^8373*100000000000000^6325 ≤ 10941725719113^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879841889 10000000000 10941725719113 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209117797/2000000000 : ℝ)^8373 ≤ (10273055810399/20000000000000 : ℝ)^6325 := by
    have hnat : (1209117797 : ℕ)^8373*20000000000000^6325 ≤ 10273055810399^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209117797 2000000000 10273055810399 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392629687/5000000000 : ℝ)^8373 ≤ (37692995206371/100000000000000 : ℝ)^6325 := by
    have hnat : (2392629687 : ℕ)^8373*100000000000000^6325 ≤ 37692995206371^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392629687 5000000000 37692995206371 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879841889/10000000000 : ℝ), (1209117797/2000000000 : ℝ), (2392629687/5000000000 : ℝ)] ![(10941725719113/100000000000000 : ℝ), (10273055810399/20000000000000 : ℝ), (37692995206371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879841889/10000000000 : ℝ)|^8373 ≤ (10941725719113/100000000000000 : ℝ)^6325
        have hw : |(-1879841889/10000000000 : ℝ)|=(1879841889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209117797/2000000000 : ℝ)|^8373 ≤ (10273055810399/20000000000000 : ℝ)^6325
        have hw : |(1209117797/2000000000 : ℝ)|=(1209117797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2392629687/5000000000 : ℝ)|^8373 ≤ (37692995206371/100000000000000 : ℝ)^6325
        have hw : |(2392629687/5000000000 : ℝ)|=(2392629687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s0_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5514652733/10000000000 : ℝ)*x 0 + (-650514051/2500000000 : ℝ)*x 1 + (1531283/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514652733/10000000000 : ℝ)^8373 ≤ (22740142785363/50000000000000 : ℝ)^6325 := by
    have hnat : (5514652733 : ℕ)^8373*50000000000000^6325 ≤ 22740142785363^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514652733 10000000000 22740142785363 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650514051/2500000000 : ℝ)^8373 ≤ (3365343838061/20000000000000 : ℝ)^6325 := by
    have hnat : (650514051 : ℕ)^8373*20000000000000^6325 ≤ 3365343838061^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650514051 2500000000 3365343838061 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1531283/3200000 : ℝ)^8373 ≤ (18846497608399/50000000000000 : ℝ)^6325 := by
    have hnat : (1531283 : ℕ)^8373*50000000000000^6325 ≤ 18846497608399^6325*3200000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531283 3200000 18846497608399 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514652733/10000000000 : ℝ), (-650514051/2500000000 : ℝ), (1531283/3200000 : ℝ)] ![(22740142785363/50000000000000 : ℝ), (3365343838061/20000000000000 : ℝ), (18846497608399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514652733/10000000000 : ℝ)|^8373 ≤ (22740142785363/50000000000000 : ℝ)^6325
        have hw : |(5514652733/10000000000 : ℝ)|=(5514652733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-650514051/2500000000 : ℝ)|^8373 ≤ (3365343838061/20000000000000 : ℝ)^6325
        have hw : |(-650514051/2500000000 : ℝ)|=(650514051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1531283/3200000 : ℝ)|^8373 ≤ (18846497608399/50000000000000 : ℝ)^6325
        have hw : |(1531283/3200000 : ℝ)|=(1531283/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s0_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5514652707/10000000000 : ℝ)*x 0 + (598157423/1250000000 : ℝ)*x 1 + (-2602056227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514652707/10000000000 : ℝ)^8373 ≤ (4548028528687/10000000000000 : ℝ)^6325 := by
    have hnat : (5514652707 : ℕ)^8373*10000000000000^6325 ≤ 4548028528687^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514652707 10000000000 4548028528687 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598157423/1250000000 : ℝ)^8373 ≤ (7538599062129/20000000000000 : ℝ)^6325 := by
    have hnat : (598157423 : ℕ)^8373*20000000000000^6325 ≤ 7538599062129^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598157423 1250000000 7538599062129 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602056227/10000000000 : ℝ)^8373 ≤ (8413359693599/50000000000000 : ℝ)^6325 := by
    have hnat : (2602056227 : ℕ)^8373*50000000000000^6325 ≤ 8413359693599^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602056227 10000000000 8413359693599 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514652707/10000000000 : ℝ), (598157423/1250000000 : ℝ), (-2602056227/10000000000 : ℝ)] ![(4548028528687/10000000000000 : ℝ), (7538599062129/20000000000000 : ℝ), (8413359693599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514652707/10000000000 : ℝ)|^8373 ≤ (4548028528687/10000000000000 : ℝ)^6325
        have hw : |(5514652707/10000000000 : ℝ)|=(5514652707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598157423/1250000000 : ℝ)|^8373 ≤ (7538599062129/20000000000000 : ℝ)^6325
        have hw : |(598157423/1250000000 : ℝ)|=(598157423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2602056227/10000000000 : ℝ)|^8373 ≤ (8413359693599/50000000000000 : ℝ)^6325
        have hw : |(-2602056227/10000000000 : ℝ)|=(2602056227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s0_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33583479/80000000 : ℝ)*x 0 + (3119383151/10000000000 : ℝ)*x 1 + (5645478763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33583479/80000000 : ℝ)^8373 ≤ (3169397721997/10000000000000 : ℝ)^6325 := by
    have hnat : (33583479 : ℕ)^8373*10000000000000^6325 ≤ 3169397721997^6325*80000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33583479 80000000 3169397721997 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119383151/10000000000 : ℝ)^8373 ≤ (5347994876369/25000000000000 : ℝ)^6325 := by
    have hnat : (3119383151 : ℕ)^8373*25000000000000^6325 ≤ 5347994876369^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119383151 10000000000 5347994876369 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5645478763/10000000000 : ℝ)^8373 ≤ (23457021627651/50000000000000 : ℝ)^6325 := by
    have hnat : (5645478763 : ℕ)^8373*50000000000000^6325 ≤ 23457021627651^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5645478763 10000000000 23457021627651 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33583479/80000000 : ℝ), (3119383151/10000000000 : ℝ), (5645478763/10000000000 : ℝ)] ![(3169397721997/10000000000000 : ℝ), (5347994876369/25000000000000 : ℝ), (23457021627651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33583479/80000000 : ℝ)|^8373 ≤ (3169397721997/10000000000000 : ℝ)^6325
        have hw : |(33583479/80000000 : ℝ)|=(33583479/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119383151/10000000000 : ℝ)|^8373 ≤ (5347994876369/25000000000000 : ℝ)^6325
        have hw : |(3119383151/10000000000 : ℝ)|=(3119383151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5645478763/10000000000 : ℝ)|^8373 ≤ (23457021627651/50000000000000 : ℝ)^6325
        have hw : |(5645478763/10000000000 : ℝ)|=(5645478763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s0_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-9424383/50000000 : ℝ)*x 0 + (481775223/1000000000 : ℝ)*x 1 + (1502987753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9424383/50000000 : ℝ)^8373 ≤ (1372567010949/12500000000000 : ℝ)^6325 := by
    have hnat : (9424383 : ℕ)^8373*12500000000000^6325 ≤ 1372567010949^6325*50000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9424383 50000000 1372567010949 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481775223/1000000000 : ℝ)^8373 ≤ (38032182871081/100000000000000 : ℝ)^6325 := by
    have hnat : (481775223 : ℕ)^8373*100000000000000^6325 ≤ 38032182871081^6325*1000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481775223 1000000000 38032182871081 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1502987753/2500000000 : ℝ)^8373 ≤ (50987281027707/100000000000000 : ℝ)^6325 := by
    have hnat : (1502987753 : ℕ)^8373*100000000000000^6325 ≤ 50987281027707^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502987753 2500000000 50987281027707 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9424383/50000000 : ℝ), (481775223/1000000000 : ℝ), (1502987753/2500000000 : ℝ)] ![(1372567010949/12500000000000 : ℝ), (38032182871081/100000000000000 : ℝ), (50987281027707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9424383/50000000 : ℝ)|^8373 ≤ (1372567010949/12500000000000 : ℝ)^6325
        have hw : |(-9424383/50000000 : ℝ)|=(9424383/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481775223/1000000000 : ℝ)|^8373 ≤ (38032182871081/100000000000000 : ℝ)^6325
        have hw : |(481775223/1000000000 : ℝ)|=(481775223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1502987753/2500000000 : ℝ)|^8373 ≤ (50987281027707/100000000000000 : ℝ)^6325
        have hw : |(1502987753/2500000000 : ℝ)|=(1502987753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s0_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586006127/5000000000 : ℝ)*x 0 + (-687682391/5000000000 : ℝ)*x 1 + (1502987683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586006127/5000000000 : ℝ)^8373 ≤ (10444414501109/25000000000000 : ℝ)^6325 := by
    have hnat : (2586006127 : ℕ)^8373*25000000000000^6325 ≤ 10444414501109^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586006127 5000000000 10444414501109 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687682391/5000000000 : ℝ)^8373 ≤ (7235064096859/100000000000000 : ℝ)^6325 := by
    have hnat : (687682391 : ℕ)^8373*100000000000000^6325 ≤ 7235064096859^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687682391 5000000000 7235064096859 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1502987683/2500000000 : ℝ)^8373 ≤ (50987277884123/100000000000000 : ℝ)^6325 := by
    have hnat : (1502987683 : ℕ)^8373*100000000000000^6325 ≤ 50987277884123^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502987683 2500000000 50987277884123 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586006127/5000000000 : ℝ), (-687682391/5000000000 : ℝ), (1502987683/2500000000 : ℝ)] ![(10444414501109/25000000000000 : ℝ), (7235064096859/100000000000000 : ℝ), (50987277884123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586006127/5000000000 : ℝ)|^8373 ≤ (10444414501109/25000000000000 : ℝ)^6325
        have hw : |(2586006127/5000000000 : ℝ)|=(2586006127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-687682391/5000000000 : ℝ)|^8373 ≤ (7235064096859/100000000000000 : ℝ)^6325
        have hw : |(-687682391/5000000000 : ℝ)|=(687682391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1502987683/2500000000 : ℝ)|^8373 ≤ (50987277884123/100000000000000 : ℝ)^6325
        have hw : |(1502987683/2500000000 : ℝ)|=(1502987683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s0_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172012203/10000000000 : ℝ)*x 0 + (48095607/80000000 : ℝ)*x 1 + (-137536463/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172012203/10000000000 : ℝ)^8373 ≤ (20888828729543/50000000000000 : ℝ)^6325 := by
    have hnat : (5172012203 : ℕ)^8373*50000000000000^6325 ≤ 20888828729543^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172012203 10000000000 20888828729543 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48095607/80000000 : ℝ)^8373 ≤ (12746819872399/25000000000000 : ℝ)^6325 := by
    have hnat : (48095607 : ℕ)^8373*25000000000000^6325 ≤ 12746819872399^6325*80000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48095607 80000000 12746819872399 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137536463/1000000000 : ℝ)^8373 ≤ (1808765759591/25000000000000 : ℝ)^6325 := by
    have hnat : (137536463 : ℕ)^8373*25000000000000^6325 ≤ 1808765759591^6325*1000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137536463 1000000000 1808765759591 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172012203/10000000000 : ℝ), (48095607/80000000 : ℝ), (-137536463/1000000000 : ℝ)] ![(20888828729543/50000000000000 : ℝ), (12746819872399/25000000000000 : ℝ), (1808765759591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172012203/10000000000 : ℝ)|^8373 ≤ (20888828729543/50000000000000 : ℝ)^6325
        have hw : |(5172012203/10000000000 : ℝ)|=(5172012203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48095607/80000000 : ℝ)|^8373 ≤ (12746819872399/25000000000000 : ℝ)^6325
        have hw : |(48095607/80000000 : ℝ)|=(48095607/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137536463/1000000000 : ℝ)|^8373 ≤ (1808765759591/25000000000000 : ℝ)^6325
        have hw : |(-137536463/1000000000 : ℝ)|=(137536463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s0_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052006527/2500000000 : ℝ)*x 0 + (2790176261/5000000000 : ℝ)*x 1 + (1593402257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052006527/2500000000 : ℝ)^8373 ≤ (31794873402149/100000000000000 : ℝ)^6325 := by
    have hnat : (1052006527 : ℕ)^8373*100000000000000^6325 ≤ 31794873402149^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052006527 2500000000 31794873402149 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2790176261/5000000000 : ℝ)^8373 ≤ (9239789345581/20000000000000 : ℝ)^6325 := by
    have hnat : (2790176261 : ℕ)^8373*20000000000000^6325 ≤ 9239789345581^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790176261 5000000000 9239789345581 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593402257/5000000000 : ℝ)^8373 ≤ (11003089926779/50000000000000 : ℝ)^6325 := by
    have hnat : (1593402257 : ℕ)^8373*50000000000000^6325 ≤ 11003089926779^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593402257 5000000000 11003089926779 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052006527/2500000000 : ℝ), (2790176261/5000000000 : ℝ), (1593402257/5000000000 : ℝ)] ![(31794873402149/100000000000000 : ℝ), (9239789345581/20000000000000 : ℝ), (11003089926779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052006527/2500000000 : ℝ)|^8373 ≤ (31794873402149/100000000000000 : ℝ)^6325
        have hw : |(1052006527/2500000000 : ℝ)|=(1052006527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2790176261/5000000000 : ℝ)|^8373 ≤ (9239789345581/20000000000000 : ℝ)^6325
        have hw : |(2790176261/5000000000 : ℝ)|=(2790176261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593402257/5000000000 : ℝ)|^8373 ≤ (11003089926779/50000000000000 : ℝ)^6325
        have hw : |(1593402257/5000000000 : ℝ)|=(1593402257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (569/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2767/10000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (2093/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2093 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2093*1^512 ≤ 0^512*1^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2093/512 : ℝ) ≤ (590479436555864307/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2093 ≤ (590479436555864307/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2093*25000000000000000000^512 ≤ 590479436555864307^512*5^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 590479436555864307 25000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (590479436555864307/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2093 := by
      have hnat : (1 : ℕ)^512*1^2093 ≤ 1^2093*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25590479436555864307/25000000000000000000 : ℝ) ≤ (10057269986146099/10000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (25590479436555864307/25000000000000000000 : ℝ)^512 ≤ (10057269986146099/10000000000000000 : ℝ)^2093 := by
      have hnat : (25590479436555864307 : ℕ)^512*10000000000000000^2093 ≤ 10057269986146099^2093*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25590479436555864307 25000000000000000000 10057269986146099 10000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057269986146099/10000000000000000 : ℝ)) (X := (25590479436555864307/25000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13090479436555864307/12500000000000000000 : ℝ) ≤ (5057269986146099/5000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (13090479436555864307/12500000000000000000 : ℝ)^512 ≤ (5057269986146099/5000000000000000 : ℝ)^2093 := by
      have hnat : (13090479436555864307 : ℕ)^512*5000000000000000^2093 ≤ 5057269986146099^2093*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13090479436555864307 12500000000000000000 5057269986146099 5000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057269986146099/5000000000000000 : ℝ)) (X := (13090479436555864307/12500000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57269986146099/4000000000000000 : ℝ)*(0 : ℝ))^(2093/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(57269986146099/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(590479436555864307/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57269986146099/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (1 : ℝ)+(57269986146099/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057269986146099/10000000000000000 : ℝ) by norm_num, show 1+(590479436555864307/25000000000000000000 : ℝ)+(0 : ℝ)=(25590479436555864307/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(590479436555864307/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57269986146099/4000000000000000 : ℝ)*(2/5 : ℝ))^(2093/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(57269986146099/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057269986146099/5000000000000000 : ℝ) by norm_num, show 1+2*(590479436555864307/25000000000000000000 : ℝ)=(13090479436555864307/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57269986146099/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57269986146099/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57269986146099/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57269986146099/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57269986146099/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57269986146099/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1879841889/10000000000 : ℝ)*X 0 0+(1209117797/2000000000 : ℝ)*X 0 1+(2392629687/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5514652733/10000000000 : ℝ)*X 1 0+(-650514051/2500000000 : ℝ)*X 1 1+(1531283/3200000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5514652707/10000000000 : ℝ)*X 2 0+(598157423/1250000000 : ℝ)*X 2 1+(-2602056227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33583479/80000000 : ℝ)*X 0 0+(3119383151/10000000000 : ℝ)*X 0 1+(5645478763/10000000000 : ℝ)*X 0 2+(33583479/80000000 : ℝ)*X 1 0+(3119383151/10000000000 : ℝ)*X 1 1+(5645478763/10000000000 : ℝ)*X 1 2+(33583479/80000000 : ℝ)*X 2 0+(3119383151/10000000000 : ℝ)*X 2 1+(5645478763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9424383/50000000 : ℝ)*X 0 0+(481775223/1000000000 : ℝ)*X 0 1+(1502987753/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586006127/5000000000 : ℝ)*X 1 0+(-687682391/5000000000 : ℝ)*X 1 1+(1502987683/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5172012203/10000000000 : ℝ)*X 2 0+(48095607/80000000 : ℝ)*X 2 1+(-137536463/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052006527/2500000000 : ℝ)*X 0 0+(2790176261/5000000000 : ℝ)*X 0 1+(1593402257/5000000000 : ℝ)*X 0 2+(1052006527/2500000000 : ℝ)*X 1 0+(2790176261/5000000000 : ℝ)*X 1 1+(1593402257/5000000000 : ℝ)*X 1 2+(1052006527/2500000000 : ℝ)*X 2 0+(2790176261/5000000000 : ℝ)*X 2 1+(1593402257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392220872849496838562763/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20701177/50000000000000 : ℝ)*(base1) + (96445263/10000000000000 : ℝ)*(base19) + (896031717/100000000000000 : ℝ)*(base23) + (16170009/25000000000000 : ℝ)*(base24) + (222325111/100000000000000 : ℝ)*(upper3) + (297329817589021/50000000000000 : ℝ)*(major0) + (297329817589021/50000000000000 : ℝ)*(major1) + (297329817589021/50000000000000 : ℝ)*(major2) + (793446488161201/100000000000000 : ℝ)*(sp0) + (198361902248811/25000000000000 : ℝ)*(sp1) + (396723806368061/50000000000000 : ℝ)*(sp2) + (395868828708173/100000000000000 : ℝ)*(sp3) + (531672257/25000000000000 : ℝ)*(sp4) + (1696057387/100000000000000 : ℝ)*(sp7) + (197935283083957/50000000000000 : ℝ)*(f.failure) + (6347588587583/800000000000 : ℝ)*(f.sum) + (53623676179079/100000000000000000000000000000 : ℝ)*base65 + (582131668020921/200000000000000000000000000000 : ℝ)*base68 + (676859758979079/200000000000000000000000000000 : ℝ)*base69 + (674424639779079/200000000000000000000000000000 : ℝ)*base71 + (234324291720921/100000000000000000000000000000 : ℝ)*base74 + (1781026160979079/200000000000000000000000000000 : ℝ)*base75 + (356651440620921/200000000000000000000000000000 : ℝ)*base78 + (358684752620921/200000000000000000000000000000 : ℝ)*base80 + (222169322079079/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (16258061/5000000000000000000000 : ℝ)*base89 + (16258061/5000000000000000000000 : ℝ)*base91 + (16258061/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62058922138488591713073/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57544997/100000000000000 : ℝ)*(base1) + (313638381/25000000000000 : ℝ)*(base19) + (78044223/6250000000000 : ℝ)*(base23) + (131151343/100000000000000 : ℝ)*(upper3) + (152214197/100000000000000 : ℝ)*(upper5) + (156896449072209/25000000000000 : ℝ)*(major0) + (156896449072209/25000000000000 : ℝ)*(major1) + (156896449072209/25000000000000 : ℝ)*(major2) + (2536321193/100000000000000 : ℝ)*(sp1) + (2572717879/100000000000000 : ℝ)*(sp2) + (16747633206763/2000000000000 : ℝ)*(sp4) + (209344452979609/25000000000000 : ℝ)*(sp5) + (418688890683853/50000000000000 : ℝ)*(sp6) + (417789766749061/100000000000000 : ℝ)*(sp7) + (208894912147029/50000000000000 : ℝ)*(f.failure) + (837381602793153/100000000000000 : ℝ)*(f.sum) + (60777654737309/50000000000000000000000000000 : ℝ)*base66 + (164173559537309/100000000000000000000000000000 : ℝ)*base68 + (248744840737309/100000000000000000000000000000 : ℝ)*base70 + (58894905437309/100000000000000000000000000000 : ℝ)*base72 + (62229401237309/50000000000000000000000000000 : ℝ)*base74 + (221832986562691/100000000000000000000000000000 : ℝ)*base75 + (84192861237309/100000000000000000000000000000 : ℝ)*base78 + (142206961862691/100000000000000000000000000000 : ℝ)*base79 + (37129927387309/50000000000000000000000000000 : ℝ)*base82 + (36185517/5000000000000000000000 : ℝ)*base89 + (36185517/5000000000000000000000 : ℝ)*base91 + (36185517/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1180_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2767/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1180_s1_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-260219603/1250000000 : ℝ)*x 0 + (88929207/156250000 : ℝ)*x 1 + (501012479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260219603/1250000000 : ℝ)^8373 ≤ (12523952203293/100000000000000 : ℝ)^6325 := by
    have hnat : (260219603 : ℕ)^8373*100000000000000^6325 ≤ 12523952203293^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260219603 1250000000 12523952203293 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88929207/156250000 : ℝ)^8373 ≤ (2963789970979/6250000000000 : ℝ)^6325 := by
    have hnat : (88929207 : ℕ)^8373*6250000000000^6325 ≤ 2963789970979^6325*156250000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88929207 156250000 2963789970979 6250000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501012479/1000000000 : ℝ)^8373 ≤ (20027704122653/50000000000000 : ℝ)^6325 := by
    have hnat : (501012479 : ℕ)^8373*50000000000000^6325 ≤ 20027704122653^6325*1000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501012479 1000000000 20027704122653 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260219603/1250000000 : ℝ), (88929207/156250000 : ℝ), (501012479/1000000000 : ℝ)] ![(12523952203293/100000000000000 : ℝ), (2963789970979/6250000000000 : ℝ), (20027704122653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260219603/1250000000 : ℝ)|^8373 ≤ (12523952203293/100000000000000 : ℝ)^6325
        have hw : |(-260219603/1250000000 : ℝ)|=(260219603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88929207/156250000 : ℝ)|^8373 ≤ (2963789970979/6250000000000 : ℝ)^6325
        have hw : |(88929207/156250000 : ℝ)|=(88929207/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501012479/1000000000 : ℝ)|^8373 ≤ (20027704122653/50000000000000 : ℝ)^6325
        have hw : |(501012479/1000000000 : ℝ)|=(501012479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s1_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417038927/10000000000 : ℝ)*x 0 + (-2448741057/10000000000 : ℝ)*x 1 + (5010124979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417038927/10000000000 : ℝ)^8373 ≤ (44417647295531/100000000000000 : ℝ)^6325 := by
    have hnat : (5417038927 : ℕ)^8373*100000000000000^6325 ≤ 44417647295531^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417038927 10000000000 44417647295531 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2448741057/10000000000 : ℝ)^8373 ≤ (1940867806137/12500000000000 : ℝ)^6325 := by
    have hnat : (2448741057 : ℕ)^8373*12500000000000^6325 ≤ 1940867806137^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2448741057 10000000000 1940867806137 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5010124979/10000000000 : ℝ)^8373 ≤ (8011082049121/20000000000000 : ℝ)^6325 := by
    have hnat : (5010124979 : ℕ)^8373*20000000000000^6325 ≤ 8011082049121^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010124979 10000000000 8011082049121 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417038927/10000000000 : ℝ), (-2448741057/10000000000 : ℝ), (5010124979/10000000000 : ℝ)] ![(44417647295531/100000000000000 : ℝ), (1940867806137/12500000000000 : ℝ), (8011082049121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417038927/10000000000 : ℝ)|^8373 ≤ (44417647295531/100000000000000 : ℝ)^6325
        have hw : |(5417038927/10000000000 : ℝ)|=(5417038927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2448741057/10000000000 : ℝ)|^8373 ≤ (1940867806137/12500000000000 : ℝ)^6325
        have hw : |(-2448741057/10000000000 : ℝ)|=(2448741057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5010124979/10000000000 : ℝ)|^8373 ≤ (8011082049121/20000000000000 : ℝ)^6325
        have hw : |(5010124979/10000000000 : ℝ)|=(5010124979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s1_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108340763/200000000 : ℝ)*x 0 + (5010125509/10000000000 : ℝ)*x 1 + (-153046337/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108340763/200000000 : ℝ)^8373 ≤ (44417638861501/100000000000000 : ℝ)^6325 := by
    have hnat : (108340763 : ℕ)^8373*100000000000000^6325 ≤ 44417638861501^6325*200000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108340763 200000000 44417638861501 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5010125509/10000000000 : ℝ)^8373 ≤ (4005541585491/10000000000000 : ℝ)^6325 := by
    have hnat : (5010125509 : ℕ)^8373*10000000000000^6325 ≤ 4005541585491^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010125509 10000000000 4005541585491 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153046337/625000000 : ℝ)^8373 ≤ (15526945261051/100000000000000 : ℝ)^6325 := by
    have hnat : (153046337 : ℕ)^8373*100000000000000^6325 ≤ 15526945261051^6325*625000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153046337 625000000 15526945261051 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108340763/200000000 : ℝ), (5010125509/10000000000 : ℝ), (-153046337/625000000 : ℝ)] ![(44417638861501/100000000000000 : ℝ), (4005541585491/10000000000000 : ℝ), (15526945261051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108340763/200000000 : ℝ)|^8373 ≤ (44417638861501/100000000000000 : ℝ)^6325
        have hw : |(108340763/200000000 : ℝ)|=(108340763/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5010125509/10000000000 : ℝ)|^8373 ≤ (4005541585491/10000000000000 : ℝ)^6325
        have hw : |(5010125509/10000000000 : ℝ)|=(5010125509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153046337/625000000 : ℝ)|^8373 ≤ (15526945261051/100000000000000 : ℝ)^6325
        have hw : |(-153046337/625000000 : ℝ)|=(153046337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s1_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2157101039/5000000000 : ℝ)*x 0 + (3684126959/10000000000 : ℝ)*x 1 + (5049754919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157101039/5000000000 : ℝ)^8373 ≤ (8215297389187/25000000000000 : ℝ)^6325 := by
    have hnat : (2157101039 : ℕ)^8373*25000000000000^6325 ≤ 8215297389187^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157101039 5000000000 8215297389187 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3684126959/10000000000 : ℝ)^8373 ≤ (6665859200591/25000000000000 : ℝ)^6325 := by
    have hnat : (3684126959 : ℕ)^8373*25000000000000^6325 ≤ 6665859200591^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3684126959 10000000000 6665859200591 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5049754919/10000000000 : ℝ)^8373 ≤ (40475373619749/100000000000000 : ℝ)^6325 := by
    have hnat : (5049754919 : ℕ)^8373*100000000000000^6325 ≤ 40475373619749^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049754919 10000000000 40475373619749 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157101039/5000000000 : ℝ), (3684126959/10000000000 : ℝ), (5049754919/10000000000 : ℝ)] ![(8215297389187/25000000000000 : ℝ), (6665859200591/25000000000000 : ℝ), (40475373619749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157101039/5000000000 : ℝ)|^8373 ≤ (8215297389187/25000000000000 : ℝ)^6325
        have hw : |(2157101039/5000000000 : ℝ)|=(2157101039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3684126959/10000000000 : ℝ)|^8373 ≤ (6665859200591/25000000000000 : ℝ)^6325
        have hw : |(3684126959/10000000000 : ℝ)|=(3684126959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5049754919/10000000000 : ℝ)|^8373 ≤ (40475373619749/100000000000000 : ℝ)^6325
        have hw : |(5049754919/10000000000 : ℝ)|=(5049754919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s1_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-104125621/500000000 : ℝ)*x 0 + (2509646937/5000000000 : ℝ)*x 1 + (5682120309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104125621/500000000 : ℝ)^8373 ≤ (3132492533329/25000000000000 : ℝ)^6325 := by
    have hnat : (104125621 : ℕ)^8373*25000000000000^6325 ≤ 3132492533329^6325*500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104125621 500000000 3132492533329 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509646937/5000000000 : ℝ)^8373 ≤ (40152478850431/100000000000000 : ℝ)^6325 := by
    have hnat : (2509646937 : ℕ)^8373*100000000000000^6325 ≤ 40152478850431^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509646937 5000000000 40152478850431 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5682120309/10000000000 : ℝ)^8373 ≤ (47317551005417/100000000000000 : ℝ)^6325 := by
    have hnat : (5682120309 : ℕ)^8373*100000000000000^6325 ≤ 47317551005417^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682120309 10000000000 47317551005417 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104125621/500000000 : ℝ), (2509646937/5000000000 : ℝ), (5682120309/10000000000 : ℝ)] ![(3132492533329/25000000000000 : ℝ), (40152478850431/100000000000000 : ℝ), (47317551005417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104125621/500000000 : ℝ)|^8373 ≤ (3132492533329/25000000000000 : ℝ)^6325
        have hw : |(-104125621/500000000 : ℝ)|=(104125621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509646937/5000000000 : ℝ)|^8373 ≤ (40152478850431/100000000000000 : ℝ)^6325
        have hw : |(2509646937/5000000000 : ℝ)|=(2509646937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5682120309/10000000000 : ℝ)|^8373 ≤ (47317551005417/100000000000000 : ℝ)^6325
        have hw : |(5682120309/10000000000 : ℝ)|=(5682120309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s1_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1310506277/2500000000 : ℝ)*x 0 + (-888372009/5000000000 : ℝ)*x 1 + (5682122267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310506277/2500000000 : ℝ)^8373 ≤ (42527950766759/100000000000000 : ℝ)^6325 := by
    have hnat : (1310506277 : ℕ)^8373*100000000000000^6325 ≤ 42527950766759^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310506277 2500000000 42527950766759 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888372009/5000000000 : ℝ)^8373 ≤ (2030895326267/20000000000000 : ℝ)^6325 := by
    have hnat : (888372009 : ℕ)^8373*20000000000000^6325 ≤ 2030895326267^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888372009 5000000000 2030895326267 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5682122267/10000000000 : ℝ)^8373 ≤ (5914696573759/12500000000000 : ℝ)^6325 := by
    have hnat : (5682122267 : ℕ)^8373*12500000000000^6325 ≤ 5914696573759^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682122267 10000000000 5914696573759 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310506277/2500000000 : ℝ), (-888372009/5000000000 : ℝ), (5682122267/10000000000 : ℝ)] ![(42527950766759/100000000000000 : ℝ), (2030895326267/20000000000000 : ℝ), (5914696573759/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310506277/2500000000 : ℝ)|^8373 ≤ (42527950766759/100000000000000 : ℝ)^6325
        have hw : |(1310506277/2500000000 : ℝ)|=(1310506277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888372009/5000000000 : ℝ)|^8373 ≤ (2030895326267/20000000000000 : ℝ)^6325
        have hw : |(-888372009/5000000000 : ℝ)|=(888372009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5682122267/10000000000 : ℝ)|^8373 ≤ (5914696573759/12500000000000 : ℝ)^6325
        have hw : |(5682122267/10000000000 : ℝ)|=(5682122267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s1_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621012351/5000000000 : ℝ)*x 0 + (5682123241/10000000000 : ℝ)*x 1 + (-888371587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621012351/5000000000 : ℝ)^8373 ≤ (42527946406403/100000000000000 : ℝ)^6325 := by
    have hnat : (2621012351 : ℕ)^8373*100000000000000^6325 ≤ 42527946406403^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621012351 5000000000 42527946406403 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5682123241/10000000000 : ℝ)^8373 ≤ (47317583327281/100000000000000 : ℝ)^6325 := by
    have hnat : (5682123241 : ℕ)^8373*100000000000000^6325 ≤ 47317583327281^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682123241 10000000000 47317583327281 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888371587/5000000000 : ℝ)^8373 ≤ (158663597591/1562500000000 : ℝ)^6325 := by
    have hnat : (888371587 : ℕ)^8373*1562500000000^6325 ≤ 158663597591^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888371587 5000000000 158663597591 1562500000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621012351/5000000000 : ℝ), (5682123241/10000000000 : ℝ), (-888371587/5000000000 : ℝ)] ![(42527946406403/100000000000000 : ℝ), (47317583327281/100000000000000 : ℝ), (158663597591/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621012351/5000000000 : ℝ)|^8373 ≤ (42527946406403/100000000000000 : ℝ)^6325
        have hw : |(2621012351/5000000000 : ℝ)|=(2621012351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5682123241/10000000000 : ℝ)|^8373 ≤ (47317583327281/100000000000000 : ℝ)^6325
        have hw : |(5682123241/10000000000 : ℝ)|=(5682123241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-888371587/5000000000 : ℝ)|^8373 ≤ (158663597591/1562500000000 : ℝ)^6325
        have hw : |(-888371587/5000000000 : ℝ)|=(888371587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s1_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4315713313/10000000000 : ℝ)*x 0 + (1257844473/2500000000 : ℝ)*x 1 + (1851430651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315713313/10000000000 : ℝ)^8373 ≤ (16438214340119/50000000000000 : ℝ)^6325 := by
    have hnat : (4315713313 : ℕ)^8373*50000000000000^6325 ≤ 16438214340119^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315713313 10000000000 16438214340119 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257844473/2500000000 : ℝ)^8373 ≤ (40280496784151/100000000000000 : ℝ)^6325 := by
    have hnat : (1257844473 : ℕ)^8373*100000000000000^6325 ≤ 40280496784151^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257844473 2500000000 40280496784151 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1851430651/5000000000 : ℝ)^8373 ≤ (13421537265417/50000000000000 : ℝ)^6325 := by
    have hnat : (1851430651 : ℕ)^8373*50000000000000^6325 ≤ 13421537265417^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851430651 5000000000 13421537265417 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315713313/10000000000 : ℝ), (1257844473/2500000000 : ℝ), (1851430651/5000000000 : ℝ)] ![(16438214340119/50000000000000 : ℝ), (40280496784151/100000000000000 : ℝ), (13421537265417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315713313/10000000000 : ℝ)|^8373 ≤ (16438214340119/50000000000000 : ℝ)^6325
        have hw : |(4315713313/10000000000 : ℝ)|=(4315713313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1257844473/2500000000 : ℝ)|^8373 ≤ (40280496784151/100000000000000 : ℝ)^6325
        have hw : |(1257844473/2500000000 : ℝ)|=(1257844473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1851430651/5000000000 : ℝ)|^8373 ≤ (13421537265417/50000000000000 : ℝ)^6325
        have hw : |(1851430651/5000000000 : ℝ)|=(1851430651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2767/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (293/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20267/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2767/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (569/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2767/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (569/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2767/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (569/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2767/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (569/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2767/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (569/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2767/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (569/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (569/100000 : ℝ) ^ (2093/512 : ℝ) ≤ (13309890277/20000000000000000000 : ℝ) := by
    have hpowers : (569/100000 : ℝ)^2093 ≤ (13309890277/20000000000000000000 : ℝ)^512 := by
      have hnat : (569 : ℕ)^2093*20000000000000000000^512 ≤ 13309890277^512*100000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        569 100000 13309890277 20000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (569/100000 : ℝ)) (X := (13309890277/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2767/10000 : ℝ) ^ (2093/512 : ℝ) ≤ (104718754572924759/20000000000000000000 : ℝ) := by
    have hpowers : (2767/10000 : ℝ)^2093 ≤ (104718754572924759/20000000000000000000 : ℝ)^512 := by
      have hnat : (2767 : ℕ)^2093*20000000000000000000^512 ≤ 104718754572924759^512*10000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2767 10000 104718754572924759 20000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2767/10000 : ℝ)) (X := (104718754572924759/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000013309890277/10000000000000000000 : ℝ) ≤ (2500000000813983/2500000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (10000000013309890277/10000000000000000000 : ℝ)^512 ≤ (2500000000813983/2500000000000000 : ℝ)^2093 := by
      have hnat : (10000000013309890277 : ℕ)^512*2500000000000000^2093 ≤ 2500000000813983^2093*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000013309890277 10000000000000000000 2500000000813983 2500000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000813983/2500000000000000 : ℝ)) (X := (10000000013309890277/10000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5026179691970703759/5000000000000000000 : ℝ) ≤ (2503195789808863/2500000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (5026179691970703759/5000000000000000000 : ℝ)^512 ≤ (2503195789808863/2500000000000000 : ℝ)^2093 := by
      have hnat : (5026179691970703759 : ℕ)^512*2500000000000000^2093 ≤ 2503195789808863^2093*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5026179691970703759 5000000000000000000 2503195789808863 2500000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503195789808863/2500000000000000 : ℝ)) (X := (5026179691970703759/5000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10104718754572924759/10000000000000000000 : ℝ) ≤ (2506391578803743/2500000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (10104718754572924759/10000000000000000000 : ℝ)^512 ≤ (2506391578803743/2500000000000000 : ℝ)^2093 := by
      have hnat : (10104718754572924759 : ℕ)^512*2500000000000000^2093 ≤ 2506391578803743^2093*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10104718754572924759 10000000000000000000 2506391578803743 2500000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506391578803743/2500000000000000 : ℝ)) (X := (10104718754572924759/10000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13309890277/20000000000000000000 : ℝ) ≤ ((67748863214183579843/67752500000000000000 : ℝ)+2*(9986840609/2117265625000 : ℝ)*(569/100000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (67748863214183579843/67752500000000000000 : ℝ)+2*(9986840609/2117265625000 : ℝ)*(569/100000 : ℝ)=(2500000000813983/2500000000000000 : ℝ) by norm_num, show 1+2*(13309890277/20000000000000000000 : ℝ)=(10000000013309890277/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(104718754572924759/20000000000000000000 : ℝ)+(13309890277/20000000000000000000 : ℝ) ≤ ((67748863214183579843/67752500000000000000 : ℝ)+(9986840609/2117265625000 : ℝ)*((2767/10000 : ℝ)+(569/100000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (67748863214183579843/67752500000000000000 : ℝ)+(9986840609/2117265625000 : ℝ)*((2767/10000 : ℝ)+(569/100000 : ℝ))=(2503195789808863/2500000000000000 : ℝ) by norm_num, show 1+(104718754572924759/20000000000000000000 : ℝ)+(13309890277/20000000000000000000 : ℝ)=(5026179691970703759/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(104718754572924759/20000000000000000000 : ℝ) ≤ ((67748863214183579843/67752500000000000000 : ℝ)+2*(9986840609/2117265625000 : ℝ)*(2767/10000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (67748863214183579843/67752500000000000000 : ℝ)+2*(9986840609/2117265625000 : ℝ)*(2767/10000 : ℝ)=(2506391578803743/2500000000000000 : ℝ) by norm_num, show 1+2*(104718754572924759/20000000000000000000 : ℝ)=(10104718754572924759/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67748863214183579843/67752500000000000000 : ℝ)*(X 1 0+X 2 0)+(9986840609/2117265625000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (569/100000 : ℝ)) (hi := (2767/10000 : ℝ)) (c := (67748863214183579843/67752500000000000000 : ℝ)) (alpha := (9986840609/2117265625000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67748863214183579843/67752500000000000000 : ℝ)*(X 0 1+X 2 1)+(9986840609/2117265625000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (569/100000 : ℝ)) (hi := (2767/10000 : ℝ)) (c := (67748863214183579843/67752500000000000000 : ℝ)) (alpha := (9986840609/2117265625000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67748863214183579843/67752500000000000000 : ℝ)*(X 0 2+X 1 2)+(9986840609/2117265625000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (569/100000 : ℝ)) (hi := (2767/10000 : ℝ)) (c := (67748863214183579843/67752500000000000000 : ℝ)) (alpha := (9986840609/2117265625000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-260219603/1250000000 : ℝ)*X 0 0+(88929207/156250000 : ℝ)*X 0 1+(501012479/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5417038927/10000000000 : ℝ)*X 1 0+(-2448741057/10000000000 : ℝ)*X 1 1+(5010124979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((108340763/200000000 : ℝ)*X 2 0+(5010125509/10000000000 : ℝ)*X 2 1+(-153046337/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157101039/5000000000 : ℝ)*X 0 0+(3684126959/10000000000 : ℝ)*X 0 1+(5049754919/10000000000 : ℝ)*X 0 2+(2157101039/5000000000 : ℝ)*X 1 0+(3684126959/10000000000 : ℝ)*X 1 1+(5049754919/10000000000 : ℝ)*X 1 2+(2157101039/5000000000 : ℝ)*X 2 0+(3684126959/10000000000 : ℝ)*X 2 1+(5049754919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104125621/500000000 : ℝ)*X 0 0+(2509646937/5000000000 : ℝ)*X 0 1+(5682120309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310506277/2500000000 : ℝ)*X 1 0+(-888372009/5000000000 : ℝ)*X 1 1+(5682122267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621012351/5000000000 : ℝ)*X 2 0+(5682123241/10000000000 : ℝ)*X 2 1+(-888371587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315713313/10000000000 : ℝ)*X 0 0+(1257844473/2500000000 : ℝ)*X 0 1+(1851430651/5000000000 : ℝ)*X 0 2+(4315713313/10000000000 : ℝ)*X 1 0+(1257844473/2500000000 : ℝ)*X 1 1+(1851430651/5000000000 : ℝ)*X 1 2+(4315713313/10000000000 : ℝ)*X 2 0+(1257844473/2500000000 : ℝ)*X 2 1+(1851430651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3543597754641435149778239559/1693812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1802061/20000000000000 : ℝ)*(base16) + (309974451/50000000000000 : ℝ)*(base19) + (109173749/25000000000000 : ℝ)*(base23) + (123619/1250000000000 : ℝ)*(upper2) + (137029949/100000000000000 : ℝ)*(upper3) + (549990459735429/50000000000000 : ℝ)*(major0) + (549990459735429/50000000000000 : ℝ)*(major1) + (549990459735429/50000000000000 : ℝ)*(major2) + (29353822311251/2000000000000 : ℝ)*(sp0) + (1467693396473157/100000000000000 : ℝ)*(sp1) + (183461698592171/12500000000000 : ℝ)*(sp2) + (732265589834323/100000000000000 : ℝ)*(sp3) + (2909869813/100000000000000 : ℝ)*(sp4) + (2153938897/100000000000000 : ℝ)*(sp7) + (36613387188661/5000000000000 : ℝ)*(f.failure) + (366923506358091/25000000000000 : ℝ)*(f.sum) + (31906871869163/27101000000000000000000000000 : ℝ)*base66 + (12523148992711482647/3387625000000000000000000000000000 : ℝ)*base67 + (16118338502198357647/3387625000000000000000000000000000 : ℝ)*base69 + (4313261384382392353/3387625000000000000000000000000000 : ℝ)*base72 + (135035418873/54202000000000000000000000 : ℝ)*base73 + (26807169431875107647/3387625000000000000000000000000000 : ℝ)*base75 + (6503402675647482647/3387625000000000000000000000000000 : ℝ)*base77 + (16083421146957267353/3387625000000000000000000000000000 : ℝ)*base80 + (74796160519343/27101000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (83853/500000000000000000000 : ℝ)*base89 + (83853/500000000000000000000 : ℝ)*base91 + (83853/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1894726331656424921588123577/846906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (781019089/50000000000000 : ℝ)*(base19) + (1048721523/50000000000000 : ℝ)*(base23) + (62939811/25000000000000 : ℝ)*(upper2) + (395306143/100000000000000 : ℝ)*(upper3) + (86077923/50000000000000 : ℝ)*(upper5) + (565351699455687/50000000000000 : ℝ)*(major0) + (565351699455687/50000000000000 : ℝ)*(major1) + (565351699455687/50000000000000 : ℝ)*(major2) + (4275044829/50000000000000 : ℝ)*(sp1) + (6850682509/50000000000000 : ℝ)*(sp2) + (377171683290887/25000000000000 : ℝ)*(sp4) + (23573072203683/1562500000000 : ℝ)*(sp5) + (377167733588871/25000000000000 : ℝ)*(sp6) + (188179997521193/25000000000000 : ℝ)*(sp7) + (188179997521193/25000000000000 : ℝ)*(f.failure) + (377171683290887/25000000000000 : ℝ)*(f.sum) + (4134617704549/1355050000000000000000000000 : ℝ)*base66 + (23493679205063917141/3387625000000000000000000000000000 : ℝ)*base67 + (4416526815826417141/3387625000000000000000000000000000 : ℝ)*base69 + (9334836547048667141/3387625000000000000000000000000000 : ℝ)*base71 + (8886910963297/13550500000000000000000000000 : ℝ)*base73 + (10909011912907167141/3387625000000000000000000000000000 : ℝ)*base75 + (14933528334352082859/3387625000000000000000000000000000 : ℝ)*base78 + (34748240569282167141/3387625000000000000000000000000000 : ℝ)*base79 + (521633582561/1693812500000000000000000000 : ℝ)*base82 + (11742111/2500000000000000000000 : ℝ)*base90 + (11742111/2500000000000000000000 : ℝ)*base92 + (11742111/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1180_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2767/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (293/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20267/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1180_s2_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066486299/5000000000 : ℝ)*x 0 + (1100744351/2000000000 : ℝ)*x 1 + (2582634407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066486299/5000000000 : ℝ)^8373 ≤ (101042585861/781250000000 : ℝ)^6325 := by
    have hnat : (1066486299 : ℕ)^8373*781250000000^6325 ≤ 101042585861^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066486299 5000000000 101042585861 781250000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100744351/2000000000 : ℝ)^8373 ≤ (22680492140051/50000000000000 : ℝ)^6325 := by
    have hnat : (1100744351 : ℕ)^8373*50000000000000^6325 ≤ 22680492140051^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100744351 2000000000 22680492140051 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582634407/5000000000 : ℝ)^8373 ≤ (20852782353183/50000000000000 : ℝ)^6325 := by
    have hnat : (2582634407 : ℕ)^8373*50000000000000^6325 ≤ 20852782353183^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582634407 5000000000 20852782353183 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066486299/5000000000 : ℝ), (1100744351/2000000000 : ℝ), (2582634407/5000000000 : ℝ)] ![(101042585861/781250000000 : ℝ), (22680492140051/50000000000000 : ℝ), (20852782353183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066486299/5000000000 : ℝ)|^8373 ≤ (101042585861/781250000000 : ℝ)^6325
        have hw : |(-1066486299/5000000000 : ℝ)|=(1066486299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100744351/2000000000 : ℝ)|^8373 ≤ (22680492140051/50000000000000 : ℝ)^6325
        have hw : |(1100744351/2000000000 : ℝ)|=(1100744351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2582634407/5000000000 : ℝ)|^8373 ≤ (20852782353183/50000000000000 : ℝ)^6325
        have hw : |(2582634407/5000000000 : ℝ)|=(2582634407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s2_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335765431/625000000 : ℝ)*x 0 + (-1154339057/5000000000 : ℝ)*x 1 + (5165272233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335765431/625000000 : ℝ)^8373 ≤ (1757283977187/4000000000000 : ℝ)^6325 := by
    have hnat : (335765431 : ℕ)^8373*4000000000000^6325 ≤ 1757283977187^6325*625000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335765431 625000000 1757283977187 4000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1154339057/5000000000 : ℝ)^8373 ≤ (448821853411/3125000000000 : ℝ)^6325 := by
    have hnat : (1154339057 : ℕ)^8373*3125000000000^6325 ≤ 448821853411^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154339057 5000000000 448821853411 3125000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5165272233/10000000000 : ℝ)^8373 ≤ (20852800625381/50000000000000 : ℝ)^6325 := by
    have hnat : (5165272233 : ℕ)^8373*50000000000000^6325 ≤ 20852800625381^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165272233 10000000000 20852800625381 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335765431/625000000 : ℝ), (-1154339057/5000000000 : ℝ), (5165272233/10000000000 : ℝ)] ![(1757283977187/4000000000000 : ℝ), (448821853411/3125000000000 : ℝ), (20852800625381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335765431/625000000 : ℝ)|^8373 ≤ (1757283977187/4000000000000 : ℝ)^6325
        have hw : |(335765431/625000000 : ℝ)|=(335765431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1154339057/5000000000 : ℝ)|^8373 ≤ (448821853411/3125000000000 : ℝ)^6325
        have hw : |(-1154339057/5000000000 : ℝ)|=(1154339057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5165272233/10000000000 : ℝ)|^8373 ≤ (20852800625381/50000000000000 : ℝ)^6325
        have hw : |(5165272233/10000000000 : ℝ)|=(5165272233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s2_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343061999/2500000000 : ℝ)*x 0 + (2582635311/5000000000 : ℝ)*x 1 + (-1154339379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343061999/2500000000 : ℝ)^8373 ≤ (43932111337687/100000000000000 : ℝ)^6325 := by
    have hnat : (1343061999 : ℕ)^8373*100000000000000^6325 ≤ 43932111337687^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343061999 2500000000 43932111337687 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2582635311/5000000000 : ℝ)^8373 ≤ (1303299500981/3125000000000 : ℝ)^6325 := by
    have hnat : (2582635311 : ℕ)^8373*3125000000000^6325 ≤ 1303299500981^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582635311 5000000000 1303299500981 3125000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154339379/5000000000 : ℝ)^8373 ≤ (7181152306353/50000000000000 : ℝ)^6325 := by
    have hnat : (1154339379 : ℕ)^8373*50000000000000^6325 ≤ 7181152306353^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154339379 5000000000 7181152306353 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343061999/2500000000 : ℝ), (2582635311/5000000000 : ℝ), (-1154339379/5000000000 : ℝ)] ![(43932111337687/100000000000000 : ℝ), (1303299500981/3125000000000 : ℝ), (7181152306353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343061999/2500000000 : ℝ)|^8373 ≤ (43932111337687/100000000000000 : ℝ)^6325
        have hw : |(1343061999/2500000000 : ℝ)|=(1343061999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2582635311/5000000000 : ℝ)|^8373 ≤ (1303299500981/3125000000000 : ℝ)^6325
        have hw : |(2582635311/5000000000 : ℝ)|=(2582635311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1154339379/5000000000 : ℝ)|^8373 ≤ (7181152306353/50000000000000 : ℝ)^6325
        have hw : |(-1154339379/5000000000 : ℝ)|=(1154339379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s2_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (16989973/39062500 : ℝ)*x 0 + (2011622361/5000000000 : ℝ)*x 1 + (940321197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16989973/39062500 : ℝ)^8373 ≤ (8304225938939/25000000000000 : ℝ)^6325 := by
    have hnat : (16989973 : ℕ)^8373*25000000000000^6325 ≤ 8304225938939^6325*39062500^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16989973 39062500 8304225938939 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011622361/5000000000 : ℝ)^8373 ≤ (7489977301787/25000000000000 : ℝ)^6325 := by
    have hnat : (2011622361 : ℕ)^8373*25000000000000^6325 ≤ 7489977301787^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011622361 5000000000 7489977301787 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940321197/2000000000 : ℝ)^8373 ≤ (18411593509747/50000000000000 : ℝ)^6325 := by
    have hnat : (940321197 : ℕ)^8373*50000000000000^6325 ≤ 18411593509747^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940321197 2000000000 18411593509747 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16989973/39062500 : ℝ), (2011622361/5000000000 : ℝ), (940321197/2000000000 : ℝ)] ![(8304225938939/25000000000000 : ℝ), (7489977301787/25000000000000 : ℝ), (18411593509747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16989973/39062500 : ℝ)|^8373 ≤ (8304225938939/25000000000000 : ℝ)^6325
        have hw : |(16989973/39062500 : ℝ)|=(16989973/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2011622361/5000000000 : ℝ)|^8373 ≤ (7489977301787/25000000000000 : ℝ)^6325
        have hw : |(2011622361/5000000000 : ℝ)|=(2011622361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(940321197/2000000000 : ℝ)|^8373 ≤ (18411593509747/50000000000000 : ℝ)^6325
        have hw : |(940321197/2000000000 : ℝ)|=(940321197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s2_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133064347/10000000000 : ℝ)*x 0 + (2583771059/5000000000 : ℝ)*x 1 + (2750713439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133064347/10000000000 : ℝ)^8373 ≤ (1293418745853/10000000000000 : ℝ)^6325 := by
    have hnat : (2133064347 : ℕ)^8373*10000000000000^6325 ≤ 1293418745853^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133064347 10000000000 1293418745853 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2583771059/5000000000 : ℝ)^8373 ≤ (41729864920237/100000000000000 : ℝ)^6325 := by
    have hnat : (2583771059 : ℕ)^8373*100000000000000^6325 ≤ 41729864920237^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583771059 5000000000 41729864920237 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750713439/5000000000 : ℝ)^8373 ≤ (2833496725313/6250000000000 : ℝ)^6325 := by
    have hnat : (2750713439 : ℕ)^8373*6250000000000^6325 ≤ 2833496725313^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750713439 5000000000 2833496725313 6250000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133064347/10000000000 : ℝ), (2583771059/5000000000 : ℝ), (2750713439/5000000000 : ℝ)] ![(1293418745853/10000000000000 : ℝ), (41729864920237/100000000000000 : ℝ), (2833496725313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133064347/10000000000 : ℝ)|^8373 ≤ (1293418745853/10000000000000 : ℝ)^6325
        have hw : |(-2133064347/10000000000 : ℝ)|=(2133064347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2583771059/5000000000 : ℝ)|^8373 ≤ (41729864920237/100000000000000 : ℝ)^6325
        have hw : |(2583771059/5000000000 : ℝ)|=(2583771059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750713439/5000000000 : ℝ)|^8373 ≤ (2833496725313/6250000000000 : ℝ)^6325
        have hw : |(2750713439/5000000000 : ℝ)|=(2750713439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s2_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057231483/2000000000 : ℝ)*x 0 + (-1972522071/10000000000 : ℝ)*x 1 + (5501426883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057231483/2000000000 : ℝ)^8373 ≤ (43002567423421/100000000000000 : ℝ)^6325 := by
    have hnat : (1057231483 : ℕ)^8373*100000000000000^6325 ≤ 43002567423421^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057231483 2000000000 43002567423421 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972522071/10000000000 : ℝ)^8373 ≤ (11661484901697/100000000000000 : ℝ)^6325 := by
    have hnat : (1972522071 : ℕ)^8373*100000000000000^6325 ≤ 11661484901697^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972522071 10000000000 11661484901697 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501426883/10000000000 : ℝ)^8373 ≤ (45335947659553/100000000000000 : ℝ)^6325 := by
    have hnat : (5501426883 : ℕ)^8373*100000000000000^6325 ≤ 45335947659553^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501426883 10000000000 45335947659553 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057231483/2000000000 : ℝ), (-1972522071/10000000000 : ℝ), (5501426883/10000000000 : ℝ)] ![(43002567423421/100000000000000 : ℝ), (11661484901697/100000000000000 : ℝ), (45335947659553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057231483/2000000000 : ℝ)|^8373 ≤ (43002567423421/100000000000000 : ℝ)^6325
        have hw : |(1057231483/2000000000 : ℝ)|=(1057231483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972522071/10000000000 : ℝ)|^8373 ≤ (11661484901697/100000000000000 : ℝ)^6325
        have hw : |(-1972522071/10000000000 : ℝ)|=(1972522071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501426883/10000000000 : ℝ)|^8373 ≤ (45335947659553/100000000000000 : ℝ)^6325
        have hw : |(5501426883/10000000000 : ℝ)|=(5501426883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s2_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643078781/5000000000 : ℝ)*x 0 + (1100285377/2000000000 : ℝ)*x 1 + (-394504373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643078781/5000000000 : ℝ)^8373 ≤ (21501284503231/50000000000000 : ℝ)^6325 := by
    have hnat : (2643078781 : ℕ)^8373*50000000000000^6325 ≤ 21501284503231^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643078781 5000000000 21501284503231 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100285377/2000000000 : ℝ)^8373 ≤ (45335947681371/100000000000000 : ℝ)^6325 := by
    have hnat : (1100285377 : ℕ)^8373*100000000000000^6325 ≤ 45335947681371^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100285377 2000000000 45335947681371 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394504373/2000000000 : ℝ)^8373 ≤ (5830741644747/50000000000000 : ℝ)^6325 := by
    have hnat : (394504373 : ℕ)^8373*50000000000000^6325 ≤ 5830741644747^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394504373 2000000000 5830741644747 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643078781/5000000000 : ℝ), (1100285377/2000000000 : ℝ), (-394504373/2000000000 : ℝ)] ![(21501284503231/50000000000000 : ℝ), (45335947681371/100000000000000 : ℝ), (5830741644747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643078781/5000000000 : ℝ)|^8373 ≤ (21501284503231/50000000000000 : ℝ)^6325
        have hw : |(2643078781/5000000000 : ℝ)|=(2643078781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100285377/2000000000 : ℝ)|^8373 ≤ (45335947681371/100000000000000 : ℝ)^6325
        have hw : |(1100285377/2000000000 : ℝ)|=(1100285377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394504373/2000000000 : ℝ)|^8373 ≤ (5830741644747/50000000000000 : ℝ)^6325
        have hw : |(-394504373/2000000000 : ℝ)|=(394504373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s2_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349618881/10000000000 : ℝ)*x 0 + (587131521/1250000000 : ℝ)*x 1 + (2013921019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349618881/10000000000 : ℝ)^8373 ≤ (33218782118243/100000000000000 : ℝ)^6325 := by
    have hnat : (4349618881 : ℕ)^8373*100000000000000^6325 ≤ 33218782118243^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349618881 10000000000 33218782118243 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (587131521/1250000000 : ℝ)^8373 ≤ (9193995093043/25000000000000 : ℝ)^6325 := by
    have hnat : (587131521 : ℕ)^8373*25000000000000^6325 ≤ 9193995093043^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587131521 1250000000 9193995093043 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013921019/5000000000 : ℝ)^8373 ≤ (30005237490911/100000000000000 : ℝ)^6325 := by
    have hnat : (2013921019 : ℕ)^8373*100000000000000^6325 ≤ 30005237490911^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013921019 5000000000 30005237490911 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349618881/10000000000 : ℝ), (587131521/1250000000 : ℝ), (2013921019/5000000000 : ℝ)] ![(33218782118243/100000000000000 : ℝ), (9193995093043/25000000000000 : ℝ), (30005237490911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349618881/10000000000 : ℝ)|^8373 ≤ (33218782118243/100000000000000 : ℝ)^6325
        have hw : |(4349618881/10000000000 : ℝ)|=(4349618881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(587131521/1250000000 : ℝ)|^8373 ≤ (9193995093043/25000000000000 : ℝ)^6325
        have hw : |(587131521/1250000000 : ℝ)|=(587131521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013921019/5000000000 : ℝ)|^8373 ≤ (30005237490911/100000000000000 : ℝ)^6325
        have hw : |(2013921019/5000000000 : ℝ)|=(2013921019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20267/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (293/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (9239/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2049/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20267/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (293/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20267/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (293/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20267/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (293/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20267/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (293/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20267/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (293/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20267/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (293/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (293/5000 : ℝ) ^ (2093/512 : ℝ) ≤ (459483816637587/50000000000000000000 : ℝ) := by
    have hpowers : (293/5000 : ℝ)^2093 ≤ (459483816637587/50000000000000000000 : ℝ)^512 := by
      have hnat : (293 : ℕ)^2093*50000000000000000000^512 ≤ 459483816637587^512*5000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        293 5000 459483816637587 50000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (293/5000 : ℝ)) (X := (459483816637587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20267/100000 : ℝ) ^ (2093/512 : ℝ) ≤ (146632811946070377/100000000000000000000 : ℝ) := by
    have hpowers : (20267/100000 : ℝ)^2093 ≤ (146632811946070377/100000000000000000000 : ℝ)^512 := by
      have hnat : (20267 : ℕ)^2093*100000000000000000000^512 ≤ 146632811946070377^512*100000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20267 100000 146632811946070377 100000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20267/100000 : ℝ)) (X := (146632811946070377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000459483816637587/25000000000000000000 : ℝ) ≤ (2000008992033677/2000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (25000459483816637587/25000000000000000000 : ℝ)^512 ≤ (2000008992033677/2000000000000000 : ℝ)^2093 := by
      have hnat : (25000459483816637587 : ℕ)^512*2000000000000000^2093 ≤ 2000008992033677^2093*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000459483816637587 25000000000000000000 2000008992033677 2000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000008992033677/2000000000000000 : ℝ)) (X := (25000459483816637587/25000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100147551779579345551/100000000000000000000 : ℝ) ≤ (10003607474751239/10000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (100147551779579345551/100000000000000000000 : ℝ)^512 ≤ (10003607474751239/10000000000000000 : ℝ)^2093 := by
      have hnat : (100147551779579345551 : ℕ)^512*10000000000000000^2093 ≤ 10003607474751239^2093*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100147551779579345551 100000000000000000000 10003607474751239 10000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003607474751239/10000000000000000 : ℝ)) (X := (100147551779579345551/100000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50146632811946070377/50000000000000000000 : ℝ) ≤ (10007169989334093/10000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (50146632811946070377/50000000000000000000 : ℝ)^512 ≤ (10007169989334093/10000000000000000 : ℝ)^2093 := by
      have hnat : (50146632811946070377 : ℕ)^512*10000000000000000^2093 ≤ 10007169989334093^2093*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50146632811946070377 50000000000000000000 10007169989334093 10000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007169989334093/10000000000000000 : ℝ)) (X := (50146632811946070377/50000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(459483816637587/50000000000000000000 : ℝ) ≤ ((28805779014046974763/28814000000000000000 : ℝ)+2*(1781257291427/720350000000000 : ℝ)*(293/5000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (28805779014046974763/28814000000000000000 : ℝ)+2*(1781257291427/720350000000000 : ℝ)*(293/5000 : ℝ)=(2000008992033677/2000000000000000 : ℝ) by norm_num, show 1+2*(459483816637587/50000000000000000000 : ℝ)=(25000459483816637587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(146632811946070377/100000000000000000000 : ℝ)+(459483816637587/50000000000000000000 : ℝ) ≤ ((28805779014046974763/28814000000000000000 : ℝ)+(1781257291427/720350000000000 : ℝ)*((20267/100000 : ℝ)+(293/5000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (28805779014046974763/28814000000000000000 : ℝ)+(1781257291427/720350000000000 : ℝ)*((20267/100000 : ℝ)+(293/5000 : ℝ))=(10003607474751239/10000000000000000 : ℝ) by norm_num, show 1+(146632811946070377/100000000000000000000 : ℝ)+(459483816637587/50000000000000000000 : ℝ)=(100147551779579345551/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(146632811946070377/100000000000000000000 : ℝ) ≤ ((28805779014046974763/28814000000000000000 : ℝ)+2*(1781257291427/720350000000000 : ℝ)*(20267/100000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (28805779014046974763/28814000000000000000 : ℝ)+2*(1781257291427/720350000000000 : ℝ)*(20267/100000 : ℝ)=(10007169989334093/10000000000000000 : ℝ) by norm_num, show 1+2*(146632811946070377/100000000000000000000 : ℝ)=(50146632811946070377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28805779014046974763/28814000000000000000 : ℝ)*(X 1 0+X 2 0)+(1781257291427/720350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (293/5000 : ℝ)) (hi := (20267/100000 : ℝ)) (c := (28805779014046974763/28814000000000000000 : ℝ)) (alpha := (1781257291427/720350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28805779014046974763/28814000000000000000 : ℝ)*(X 0 1+X 2 1)+(1781257291427/720350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (293/5000 : ℝ)) (hi := (20267/100000 : ℝ)) (c := (28805779014046974763/28814000000000000000 : ℝ)) (alpha := (1781257291427/720350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28805779014046974763/28814000000000000000 : ℝ)*(X 0 2+X 1 2)+(1781257291427/720350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (293/5000 : ℝ)) (hi := (20267/100000 : ℝ)) (c := (28805779014046974763/28814000000000000000 : ℝ)) (alpha := (1781257291427/720350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066486299/5000000000 : ℝ)*X 0 0+(1100744351/2000000000 : ℝ)*X 0 1+(2582634407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335765431/625000000 : ℝ)*X 1 0+(-1154339057/5000000000 : ℝ)*X 1 1+(5165272233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343061999/2500000000 : ℝ)*X 2 0+(2582635311/5000000000 : ℝ)*X 2 1+(-1154339379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16989973/39062500 : ℝ)*X 0 0+(2011622361/5000000000 : ℝ)*X 0 1+(940321197/2000000000 : ℝ)*X 0 2+(16989973/39062500 : ℝ)*X 1 0+(2011622361/5000000000 : ℝ)*X 1 1+(940321197/2000000000 : ℝ)*X 1 2+(16989973/39062500 : ℝ)*X 2 0+(2011622361/5000000000 : ℝ)*X 2 1+(940321197/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133064347/10000000000 : ℝ)*X 0 0+(2583771059/5000000000 : ℝ)*X 0 1+(2750713439/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057231483/2000000000 : ℝ)*X 1 0+(-1972522071/10000000000 : ℝ)*X 1 1+(5501426883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643078781/5000000000 : ℝ)*X 2 0+(1100285377/2000000000 : ℝ)*X 2 1+(-394504373/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349618881/10000000000 : ℝ)*X 0 0+(587131521/1250000000 : ℝ)*X 0 1+(2013921019/5000000000 : ℝ)*X 0 2+(4349618881/10000000000 : ℝ)*X 1 0+(587131521/1250000000 : ℝ)*X 1 1+(2013921019/5000000000 : ℝ)*X 1 2+(4349618881/10000000000 : ℝ)*X 2 0+(587131521/1250000000 : ℝ)*X 2 1+(2013921019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7012996788216854569543849653/1440700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281702291/100000000000000 : ℝ)*(base19) + (772759669/100000000000000 : ℝ)*(base23) + (118273641/100000000000000 : ℝ)*(upper2) + (47516583/12500000000000 : ℝ)*(upper3) + (35895821/20000000000000 : ℝ)*(upper4) + (2214412921785323/100000000000000 : ℝ)*(major0) + (2214412921785323/100000000000000 : ℝ)*(major1) + (2214412921785323/100000000000000 : ℝ)*(major2) + (295464717592083/10000000000000 : ℝ)*(sp0) + (2954669688982973/100000000000000 : ℝ)*(sp1) + (738667299481399/25000000000000 : ℝ)*(sp2) + (1474145943476121/100000000000000 : ℝ)*(sp3) + (11397382217/50000000000000 : ℝ)*(sp4) + (9767150241/100000000000000 : ℝ)*(sp7) + (737077855313181/50000000000000 : ℝ)*(f.failure) + (184666873167829/6250000000000 : ℝ)*(f.sum) + (21754265483757/72035000000000000000000000000 : ℝ)*base65 + (12639868426364843449/2881400000000000000000000000000000 : ℝ)*base67 + (1158361780299356551/2881400000000000000000000000000000 : ℝ)*base70 + (26922823969073843449/2881400000000000000000000000000000 : ℝ)*base71 + (5936904116681/36017500000000000000000000000 : ℝ)*base73 + (8555886342688843449/2881400000000000000000000000000000 : ℝ)*base75 + (2799732196702643449/2881400000000000000000000000000000 : ℝ)*base77 + (9110531755625156551/2881400000000000000000000000000000 : ℝ)*base80 + (65695111143283/72035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (40314187/5000000000000000000000 : ℝ)*base90 + (40314187/5000000000000000000000 : ℝ)*base92 + (40314187/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10325236964642198666185874511/1440700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1706162261/100000000000000 : ℝ)*(base19) + (1840597339/100000000000000 : ℝ)*(base23) + (132131/6250000000000 : ℝ)*(upper2) + (104348521/50000000000000 : ℝ)*(upper3) + (151299937/100000000000000 : ℝ)*(upper5) + (2244672320689199/100000000000000 : ℝ)*(major0) + (2244672320689199/100000000000000 : ℝ)*(major1) + (2244672320689199/100000000000000 : ℝ)*(major2) + (16668817423/100000000000000 : ℝ)*(sp1) + (19563643647/100000000000000 : ℝ)*(sp2) + (1497522361328629/50000000000000 : ℝ)*(sp4) + (1497513173838787/50000000000000 : ℝ)*(sp5) + (187188957401017/6250000000000 : ℝ)*(sp6) + (29885993596543/2000000000000 : ℝ)*(sp7) + (29885993596543/2000000000000 : ℝ)*(f.failure) + (1497522361328629/50000000000000 : ℝ)*(f.sum) + (33436083442947/36017500000000000000000000000 : ℝ)*base66 + (5521916480822995163/2881400000000000000000000000000000 : ℝ)*base68 + (7790323353234995163/2881400000000000000000000000000000 : ℝ)*base70 + (5984534530043404837/2881400000000000000000000000000000 : ℝ)*base71 + (12121164658447/36017500000000000000000000000 : ℝ)*base74 + (429374658622795163/2881400000000000000000000000000000 : ℝ)*base76 + (24612331887077795163/2881400000000000000000000000000000 : ℝ)*base78 + (11954008748183004837/2881400000000000000000000000000000 : ℝ)*base79 + (11635738009039/18008750000000000000000000000 : ℝ)*base81 + (781561/200000000000000000000 : ℝ)*base90 + (781561/200000000000000000000 : ℝ)*base92 + (781561/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1180_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20267/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (293/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2049/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1180_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2049/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1180_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1180_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1180_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2049/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1180_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
