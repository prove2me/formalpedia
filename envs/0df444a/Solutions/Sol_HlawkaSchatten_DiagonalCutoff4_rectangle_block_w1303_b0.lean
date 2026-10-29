-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1303_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:37:18.294778+00:00
-- url     : https://prove2.me/submissions/a3986806-97ef-42b1-aad1-41199dbcdd4f

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
theorem support_rectangle_w1303_s0_0 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-114526763/625000000 : ℝ)*x 0 + (6013931761/10000000000 : ℝ)*x 1 + (960303849/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114526763/625000000 : ℝ)^4263 ≤ (5358030608243/50000000000000 : ℝ)^3239 := by
    have hnat : (114526763 : ℕ)^4263*50000000000000^3239 ≤ 5358030608243^3239*625000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114526763 625000000 5358030608243 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6013931761/10000000000 : ℝ)^4263 ≤ (25604136294897/50000000000000 : ℝ)^3239 := by
    have hnat : (6013931761 : ℕ)^4263*50000000000000^3239 ≤ 25604136294897^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013931761 10000000000 25604136294897 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960303849/2000000000 : ℝ)^4263 ≤ (19037833090849/50000000000000 : ℝ)^3239 := by
    have hnat : (960303849 : ℕ)^4263*50000000000000^3239 ≤ 19037833090849^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960303849 2000000000 19037833090849 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114526763/625000000 : ℝ), (6013931761/10000000000 : ℝ), (960303849/2000000000 : ℝ)] ![(5358030608243/50000000000000 : ℝ), (25604136294897/50000000000000 : ℝ), (19037833090849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114526763/625000000 : ℝ)|^4263 ≤ (5358030608243/50000000000000 : ℝ)^3239
        have hw : |(-114526763/625000000 : ℝ)|=(114526763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6013931761/10000000000 : ℝ)|^4263 ≤ (25604136294897/50000000000000 : ℝ)^3239
        have hw : |(6013931761/10000000000 : ℝ)|=(6013931761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(960303849/2000000000 : ℝ)|^4263 ≤ (19037833090849/50000000000000 : ℝ)^3239
        have hw : |(960303849/2000000000 : ℝ)|=(960303849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s0_1 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2753092081/5000000000 : ℝ)*x 0 + (-78860493/312500000 : ℝ)*x 1 + (600189903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753092081/5000000000 : ℝ)^4263 ≤ (45595447257769/100000000000000 : ℝ)^3239 := by
    have hnat : (2753092081 : ℕ)^4263*100000000000000^3239 ≤ 45595447257769^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753092081 5000000000 45595447257769 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78860493/312500000 : ℝ)^4263 ≤ (16328886762529/100000000000000 : ℝ)^3239 := by
    have hnat : (78860493 : ℕ)^4263*100000000000000^3239 ≤ 16328886762529^3239*312500000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78860493 312500000 16328886762529 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600189903/1250000000 : ℝ)^4263 ≤ (19037832981261/50000000000000 : ℝ)^3239 := by
    have hnat : (600189903 : ℕ)^4263*50000000000000^3239 ≤ 19037832981261^3239*1250000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600189903 1250000000 19037832981261 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753092081/5000000000 : ℝ), (-78860493/312500000 : ℝ), (600189903/1250000000 : ℝ)] ![(45595447257769/100000000000000 : ℝ), (16328886762529/100000000000000 : ℝ), (19037832981261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753092081/5000000000 : ℝ)|^4263 ≤ (45595447257769/100000000000000 : ℝ)^3239
        have hw : |(2753092081/5000000000 : ℝ)|=(2753092081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78860493/312500000 : ℝ)|^4263 ≤ (16328886762529/100000000000000 : ℝ)^3239
        have hw : |(-78860493/312500000 : ℝ)|=(78860493/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600189903/1250000000 : ℝ)|^4263 ≤ (19037832981261/50000000000000 : ℝ)^3239
        have hw : |(600189903/1250000000 : ℝ)|=(600189903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s0_2 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1376546029/2500000000 : ℝ)*x 0 + (4801519279/10000000000 : ℝ)*x 1 + (-315441971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376546029/2500000000 : ℝ)^4263 ≤ (45595446756429/100000000000000 : ℝ)^3239 := by
    have hnat : (1376546029 : ℕ)^4263*100000000000000^3239 ≤ 45595446756429^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376546029 2500000000 45595446756429 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4801519279/10000000000 : ℝ)^4263 ≤ (19037833268277/50000000000000 : ℝ)^3239 := by
    have hnat : (4801519279 : ℕ)^4263*50000000000000^3239 ≤ 19037833268277^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801519279 10000000000 19037833268277 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315441971/1250000000 : ℝ)^4263 ≤ (16328886694399/100000000000000 : ℝ)^3239 := by
    have hnat : (315441971 : ℕ)^4263*100000000000000^3239 ≤ 16328886694399^3239*1250000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315441971 1250000000 16328886694399 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1376546029/2500000000 : ℝ), (4801519279/10000000000 : ℝ), (-315441971/1250000000 : ℝ)] ![(45595446756429/100000000000000 : ℝ), (19037833268277/50000000000000 : ℝ), (16328886694399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1376546029/2500000000 : ℝ)|^4263 ≤ (45595446756429/100000000000000 : ℝ)^3239
        have hw : |(1376546029/2500000000 : ℝ)|=(1376546029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4801519279/10000000000 : ℝ)|^4263 ≤ (19037833268277/50000000000000 : ℝ)^3239
        have hw : |(4801519279/10000000000 : ℝ)|=(4801519279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315441971/1250000000 : ℝ)|^4263 ≤ (16328886694399/100000000000000 : ℝ)^3239
        have hw : |(-315441971/1250000000 : ℝ)|=(315441971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s0_3 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184645379/10000000000 : ℝ)*x 0 + (3108735057/10000000000 : ℝ)*x 1 + (1122201521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184645379/10000000000 : ℝ)^4263 ≤ (31772193315759/100000000000000 : ℝ)^3239 := by
    have hnat : (4184645379 : ℕ)^4263*100000000000000^3239 ≤ 31772193315759^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184645379 10000000000 31772193315759 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3108735057/10000000000 : ℝ)^4263 ≤ (10743247927651/50000000000000 : ℝ)^3239 := by
    have hnat : (3108735057 : ℕ)^4263*50000000000000^3239 ≤ 10743247927651^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3108735057 10000000000 10743247927651 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122201521/2000000000 : ℝ)^4263 ≤ (46741310811313/100000000000000 : ℝ)^3239 := by
    have hnat : (1122201521 : ℕ)^4263*100000000000000^3239 ≤ 46741310811313^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122201521 2000000000 46741310811313 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184645379/10000000000 : ℝ), (3108735057/10000000000 : ℝ), (1122201521/2000000000 : ℝ)] ![(31772193315759/100000000000000 : ℝ), (10743247927651/50000000000000 : ℝ), (46741310811313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184645379/10000000000 : ℝ)|^4263 ≤ (31772193315759/100000000000000 : ℝ)^3239
        have hw : |(4184645379/10000000000 : ℝ)|=(4184645379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3108735057/10000000000 : ℝ)|^4263 ≤ (10743247927651/50000000000000 : ℝ)^3239
        have hw : |(3108735057/10000000000 : ℝ)|=(3108735057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122201521/2000000000 : ℝ)|^4263 ≤ (46741310811313/100000000000000 : ℝ)^3239
        have hw : |(1122201521/2000000000 : ℝ)|=(1122201521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s0_4 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-918546553/5000000000 : ℝ)*x 0 + (2416395403/5000000000 : ℝ)*x 1 + (5981546063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918546553/5000000000 : ℝ)^4263 ≤ (2150396128437/20000000000000 : ℝ)^3239 := by
    have hnat : (918546553 : ℕ)^4263*20000000000000^3239 ≤ 2150396128437^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918546553 5000000000 2150396128437 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2416395403/5000000000 : ℝ)^4263 ≤ (38402381126409/100000000000000 : ℝ)^3239 := by
    have hnat : (2416395403 : ℕ)^4263*100000000000000^3239 ≤ 38402381126409^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416395403 5000000000 38402381126409 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5981546063/10000000000 : ℝ)^4263 ≤ (50845638211543/100000000000000 : ℝ)^3239 := by
    have hnat : (5981546063 : ℕ)^4263*100000000000000^3239 ≤ 50845638211543^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5981546063 10000000000 50845638211543 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-918546553/5000000000 : ℝ), (2416395403/5000000000 : ℝ), (5981546063/10000000000 : ℝ)] ![(2150396128437/20000000000000 : ℝ), (38402381126409/100000000000000 : ℝ), (50845638211543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-918546553/5000000000 : ℝ)|^4263 ≤ (2150396128437/20000000000000 : ℝ)^3239
        have hw : |(-918546553/5000000000 : ℝ)|=(918546553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2416395403/5000000000 : ℝ)|^4263 ≤ (38402381126409/100000000000000 : ℝ)^3239
        have hw : |(2416395403/5000000000 : ℝ)|=(2416395403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5981546063/10000000000 : ℝ)|^4263 ≤ (50845638211543/100000000000000 : ℝ)^3239
        have hw : |(5981546063/10000000000 : ℝ)|=(5981546063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s0_5 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5176031777/10000000000 : ℝ)*x 0 + (-671754543/5000000000 : ℝ)*x 1 + (1495386523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176031777/10000000000 : ℝ)^4263 ≤ (21015897357031/50000000000000 : ℝ)^3239 := by
    have hnat : (5176031777 : ℕ)^4263*50000000000000^3239 ≤ 21015897357031^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176031777 10000000000 21015897357031 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671754543/5000000000 : ℝ)^4263 ≤ (1424513347179/20000000000000 : ℝ)^3239 := by
    have hnat : (671754543 : ℕ)^4263*20000000000000^3239 ≤ 1424513347179^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671754543 5000000000 1424513347179 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1495386523/2500000000 : ℝ)^4263 ≤ (50845638535989/100000000000000 : ℝ)^3239 := by
    have hnat : (1495386523 : ℕ)^4263*100000000000000^3239 ≤ 50845638535989^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1495386523 2500000000 50845638535989 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176031777/10000000000 : ℝ), (-671754543/5000000000 : ℝ), (1495386523/2500000000 : ℝ)] ![(21015897357031/50000000000000 : ℝ), (1424513347179/20000000000000 : ℝ), (50845638535989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176031777/10000000000 : ℝ)|^4263 ≤ (21015897357031/50000000000000 : ℝ)^3239
        have hw : |(5176031777/10000000000 : ℝ)|=(5176031777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-671754543/5000000000 : ℝ)|^4263 ≤ (1424513347179/20000000000000 : ℝ)^3239
        have hw : |(-671754543/5000000000 : ℝ)|=(671754543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1495386523/2500000000 : ℝ)|^4263 ≤ (50845638535989/100000000000000 : ℝ)^3239
        have hw : |(1495386523/2500000000 : ℝ)|=(1495386523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s0_6 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1294007957/2500000000 : ℝ)*x 0 + (2990773017/5000000000 : ℝ)*x 1 + (-1343509101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294007957/2500000000 : ℝ)^4263 ≤ (164186700231/390625000000 : ℝ)^3239 := by
    have hnat : (1294007957 : ℕ)^4263*390625000000^3239 ≤ 164186700231^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294007957 2500000000 164186700231 390625000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2990773017/5000000000 : ℝ)^4263 ≤ (50845637887097/100000000000000 : ℝ)^3239 := by
    have hnat : (2990773017 : ℕ)^4263*100000000000000^3239 ≤ 50845637887097^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2990773017 5000000000 50845637887097 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343509101/10000000000 : ℝ)^4263 ≤ (3561283420279/50000000000000 : ℝ)^3239 := by
    have hnat : (1343509101 : ℕ)^4263*50000000000000^3239 ≤ 3561283420279^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343509101 10000000000 3561283420279 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294007957/2500000000 : ℝ), (2990773017/5000000000 : ℝ), (-1343509101/10000000000 : ℝ)] ![(164186700231/390625000000 : ℝ), (50845637887097/100000000000000 : ℝ), (3561283420279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294007957/2500000000 : ℝ)|^4263 ≤ (164186700231/390625000000 : ℝ)^3239
        have hw : |(1294007957/2500000000 : ℝ)|=(1294007957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2990773017/5000000000 : ℝ)|^4263 ≤ (50845637887097/100000000000000 : ℝ)^3239
        have hw : |(2990773017/5000000000 : ℝ)|=(2990773017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1343509101/10000000000 : ℝ)|^4263 ≤ (3561283420279/50000000000000 : ℝ)^3239
        have hw : |(-1343509101/10000000000 : ℝ)|=(1343509101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s0_7 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52428411/125000000 : ℝ)*x 0 + (5546466937/10000000000 : ℝ)*x 1 + (793893797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52428411/125000000 : ℝ)^4263 ≤ (31868435245813/100000000000000 : ℝ)^3239 := by
    have hnat : (52428411 : ℕ)^4263*100000000000000^3239 ≤ 31868435245813^3239*125000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52428411 125000000 31868435245813 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5546466937/10000000000 : ℝ)^4263 ≤ (9206996889899/20000000000000 : ℝ)^3239 := by
    have hnat : (5546466937 : ℕ)^4263*20000000000000^3239 ≤ 9206996889899^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5546466937 10000000000 9206996889899 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793893797/2500000000 : ℝ)^4263 ≤ (5524145073691/25000000000000 : ℝ)^3239 := by
    have hnat : (793893797 : ℕ)^4263*25000000000000^3239 ≤ 5524145073691^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793893797 2500000000 5524145073691 25000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52428411/125000000 : ℝ), (5546466937/10000000000 : ℝ), (793893797/2500000000 : ℝ)] ![(31868435245813/100000000000000 : ℝ), (9206996889899/20000000000000 : ℝ), (5524145073691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52428411/125000000 : ℝ)|^4263 ≤ (31868435245813/100000000000000 : ℝ)^3239
        have hw : |(52428411/125000000 : ℝ)|=(52428411/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5546466937/10000000000 : ℝ)|^4263 ≤ (9206996889899/20000000000000 : ℝ)^3239
        have hw : |(5546466937/10000000000 : ℝ)|=(5546466937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(793893797/2500000000 : ℝ)|^4263 ≤ (5524145073691/25000000000000 : ℝ)^3239
        have hw : |(793893797/2500000000 : ℝ)|=(793893797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1303_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13577/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2131/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2131 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2131*1^512 ≤ 0^512*1^2131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2131 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2131/512 : ℝ) ≤ (551658314137017273/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2131 ≤ (551658314137017273/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2131*25000000000000000000^512 ≤ 551658314137017273^512*5^2131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 551658314137017273 25000000000000000000 2131 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (551658314137017273/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2131 := by
      have hnat : (1 : ℕ)^512*1^2131 ≤ 1^2131*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25551658314137017273/25000000000000000000 : ℝ) ≤ (10052578445470917/10000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (25551658314137017273/25000000000000000000 : ℝ)^512 ≤ (10052578445470917/10000000000000000 : ℝ)^2131 := by
      have hnat : (25551658314137017273 : ℕ)^512*10000000000000000^2131 ≤ 10052578445470917^2131*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25551658314137017273 25000000000000000000 10052578445470917 10000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052578445470917/10000000000000000 : ℝ)) (X := (25551658314137017273/25000000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13051658314137017273/12500000000000000000 : ℝ) ≤ (5052578445470917/5000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (13051658314137017273/12500000000000000000 : ℝ)^512 ≤ (5052578445470917/5000000000000000 : ℝ)^2131 := by
      have hnat : (13051658314137017273 : ℕ)^512*5000000000000000^2131 ≤ 5052578445470917^2131*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13051658314137017273 12500000000000000000 5052578445470917 5000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5052578445470917/5000000000000000 : ℝ)) (X := (13051658314137017273/12500000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(52578445470917/4000000000000000 : ℝ)*(0 : ℝ))^(2131/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(52578445470917/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(551658314137017273/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(52578445470917/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2131/512 : ℝ) := by
    rw [show (1 : ℝ)+(52578445470917/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10052578445470917/10000000000000000 : ℝ) by norm_num, show 1+(551658314137017273/25000000000000000000 : ℝ)+(0 : ℝ)=(25551658314137017273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(551658314137017273/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(52578445470917/4000000000000000 : ℝ)*(2/5 : ℝ))^(2131/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(52578445470917/4000000000000000 : ℝ)*(2/5 : ℝ)=(5052578445470917/5000000000000000 : ℝ) by norm_num, show 1+2*(551658314137017273/25000000000000000000 : ℝ)=(13051658314137017273/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(52578445470917/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52578445470917/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(52578445470917/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52578445470917/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(52578445470917/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52578445470917/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-114526763/625000000 : ℝ)*X 0 0+(6013931761/10000000000 : ℝ)*X 0 1+(960303849/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2753092081/5000000000 : ℝ)*X 1 0+(-78860493/312500000 : ℝ)*X 1 1+(600189903/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1376546029/2500000000 : ℝ)*X 2 0+(4801519279/10000000000 : ℝ)*X 2 1+(-315441971/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4184645379/10000000000 : ℝ)*X 0 0+(3108735057/10000000000 : ℝ)*X 0 1+(1122201521/2000000000 : ℝ)*X 0 2+(4184645379/10000000000 : ℝ)*X 1 0+(3108735057/10000000000 : ℝ)*X 1 1+(1122201521/2000000000 : ℝ)*X 1 2+(4184645379/10000000000 : ℝ)*X 2 0+(3108735057/10000000000 : ℝ)*X 2 1+(1122201521/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-918546553/5000000000 : ℝ)*X 0 0+(2416395403/5000000000 : ℝ)*X 0 1+(5981546063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5176031777/10000000000 : ℝ)*X 1 0+(-671754543/5000000000 : ℝ)*X 1 1+(1495386523/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1294007957/2500000000 : ℝ)*X 2 0+(2990773017/5000000000 : ℝ)*X 2 1+(-1343509101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((52428411/125000000 : ℝ)*X 0 0+(5546466937/10000000000 : ℝ)*X 0 1+(793893797/2500000000 : ℝ)*X 0 2+(52428411/125000000 : ℝ)*X 1 0+(5546466937/10000000000 : ℝ)*X 1 1+(793893797/2500000000 : ℝ)*X 1 2+(52428411/125000000 : ℝ)*X 2 0+(5546466937/10000000000 : ℝ)*X 2 1+(793893797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33088419903637064102211/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2249329/10000000000000 : ℝ)*(base1) + (167321247/50000000000000 : ℝ)*(base19) + (65550377/20000000000000 : ℝ)*(base23) + (38068569/100000000000000 : ℝ)*(upper3) + (18930387/50000000000000 : ℝ)*(upper5) + (306110381374461/50000000000000 : ℝ)*(major0) + (306110381374461/50000000000000 : ℝ)*(major1) + (306110381374461/50000000000000 : ℝ)*(major2) + (103100347381431/12500000000000 : ℝ)*(sp0) + (824803467336001/100000000000000 : ℝ)*(sp1) + (82480347422661/10000000000000 : ℝ)*(sp2) + (399637178919757/100000000000000 : ℝ)*(sp3) + (1045420337/100000000000000 : ℝ)*(sp4) + (238994201/50000000000000 : ℝ)*(sp7) + (399637679401449/100000000000000 : ℝ)*(f.failure) + (164960760395699/20000000000000 : ℝ)*(f.sum) + (298606013649263/100000000000000000000000000000 : ℝ)*base66 + (2010950612549263/200000000000000000000000000000 : ℝ)*base68 + (722305448349263/200000000000000000000000000000 : ℝ)*base70 + (1664162502949263/200000000000000000000000000000 : ℝ)*base72 + (495642542649263/100000000000000000000000000000 : ℝ)*base74 + (1420142094949263/200000000000000000000000000000 : ℝ)*base76 + (2129744622549263/200000000000000000000000000000 : ℝ)*base78 + (1189061140549263/200000000000000000000000000000 : ℝ)*base80 + (176325353950737/100000000000000000000000000000 : ℝ)*base81 + (62819673/5000000000000000000000 : ℝ)*base89 + (62819673/5000000000000000000000 : ℝ)*base91 + (62819673/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (390810400714638858335691/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112642313/25000000000000 : ℝ)*(base19) + (459914111/100000000000000 : ℝ)*(base23) + (1371359/10000000000000 : ℝ)*(base32) + (2492083/4000000000000 : ℝ)*(upper3) + (55328013/100000000000000 : ℝ)*(upper5) + (646144837562647/100000000000000 : ℝ)*(major0) + (646144837562647/100000000000000 : ℝ)*(major1) + (646144837562647/100000000000000 : ℝ)*(major2) + (205557309/20000000000000 : ℝ)*(sp1) + (259955497/25000000000000 : ℝ)*(sp2) + (435253702346683/50000000000000 : ℝ)*(sp4) + (87050592633757/10000000000000 : ℝ)*(sp5) + (217626476239317/25000000000000 : ℝ)*(sp6) + (13180693486977/3125000000000 : ℝ)*(sp7) + (421782205296853/100000000000000 : ℝ)*(f.failure) + (435253702346683/50000000000000 : ℝ)*(f.sum) + (589094700762701/200000000000000000000000000000 : ℝ)*base66 + (592800258437299/400000000000000000000000000000 : ℝ)*base67 + (272225728037299/400000000000000000000000000000 : ℝ)*base69 + (1042882595962701/400000000000000000000000000000 : ℝ)*base72 + (854475081562701/200000000000000000000000000000 : ℝ)*base74 + (1556894056762701/400000000000000000000000000000 : ℝ)*base76 + (398554871237299/400000000000000000000000000000 : ℝ)*base77 + (3007595248762701/400000000000000000000000000000 : ℝ)*base80 + (1032083751962701/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (22586619/5000000000000000000000 : ℝ)*base90 + (22586619/5000000000000000000000 : ℝ)*base92 + (22586619/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1303_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13577/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1303_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1303_s1_0 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1011441997/5000000000 : ℝ)*x 0 + (1132014131/2000000000 : ℝ)*x 1 + (314590163/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011441997/5000000000 : ℝ)^4263 ≤ (12205506697811/100000000000000 : ℝ)^3239 := by
    have hnat : (1011441997 : ℕ)^4263*100000000000000^3239 ≤ 12205506697811^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011441997 5000000000 12205506697811 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132014131/2000000000 : ℝ)^4263 ≤ (47279974420733/100000000000000 : ℝ)^3239 := by
    have hnat : (1132014131 : ℕ)^4263*100000000000000^3239 ≤ 47279974420733^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132014131 2000000000 47279974420733 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314590163/625000000 : ℝ)^4263 ≤ (8102903773229/20000000000000 : ℝ)^3239 := by
    have hnat : (314590163 : ℕ)^4263*20000000000000^3239 ≤ 8102903773229^3239*625000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314590163 625000000 8102903773229 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1011441997/5000000000 : ℝ), (1132014131/2000000000 : ℝ), (314590163/625000000 : ℝ)] ![(12205506697811/100000000000000 : ℝ), (47279974420733/100000000000000 : ℝ), (8102903773229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1011441997/5000000000 : ℝ)|^4263 ≤ (12205506697811/100000000000000 : ℝ)^3239
        have hw : |(-1011441997/5000000000 : ℝ)|=(1011441997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132014131/2000000000 : ℝ)|^4263 ≤ (47279974420733/100000000000000 : ℝ)^3239
        have hw : |(1132014131/2000000000 : ℝ)|=(1132014131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314590163/625000000 : ℝ)|^4263 ≤ (8102903773229/20000000000000 : ℝ)^3239
        have hw : |(314590163/625000000 : ℝ)|=(314590163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s1_1 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081963087/2000000000 : ℝ)*x 0 + (-58960297/250000000 : ℝ)*x 1 + (5033442853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081963087/2000000000 : ℝ)^4263 ≤ (44548069775579/100000000000000 : ℝ)^3239 := by
    have hnat : (1081963087 : ℕ)^4263*100000000000000^3239 ≤ 44548069775579^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081963087 2000000000 44548069775579 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58960297/250000000 : ℝ)^4263 ≤ (14937408751603/100000000000000 : ℝ)^3239 := by
    have hnat : (58960297 : ℕ)^4263*100000000000000^3239 ≤ 14937408751603^3239*250000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58960297 250000000 14937408751603 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5033442853/10000000000 : ℝ)^4263 ≤ (2532157591351/6250000000000 : ℝ)^3239 := by
    have hnat : (5033442853 : ℕ)^4263*6250000000000^3239 ≤ 2532157591351^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033442853 10000000000 2532157591351 6250000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081963087/2000000000 : ℝ), (-58960297/250000000 : ℝ), (5033442853/10000000000 : ℝ)] ![(44548069775579/100000000000000 : ℝ), (14937408751603/100000000000000 : ℝ), (2532157591351/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081963087/2000000000 : ℝ)|^4263 ≤ (44548069775579/100000000000000 : ℝ)^3239
        have hw : |(1081963087/2000000000 : ℝ)|=(1081963087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58960297/250000000 : ℝ)|^4263 ≤ (14937408751603/100000000000000 : ℝ)^3239
        have hw : |(-58960297/250000000 : ℝ)|=(58960297/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5033442853/10000000000 : ℝ)|^4263 ≤ (2532157591351/6250000000000 : ℝ)^3239
        have hw : |(5033442853/10000000000 : ℝ)|=(5033442853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s1_2 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704907847/5000000000 : ℝ)*x 0 + (1258360607/2500000000 : ℝ)*x 1 + (-2358412083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704907847/5000000000 : ℝ)^4263 ≤ (5568509072829/12500000000000 : ℝ)^3239 := by
    have hnat : (2704907847 : ℕ)^4263*12500000000000^3239 ≤ 5568509072829^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704907847 5000000000 5568509072829 12500000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1258360607/2500000000 : ℝ)^4263 ≤ (40514516959269/100000000000000 : ℝ)^3239 := by
    have hnat : (1258360607 : ℕ)^4263*100000000000000^3239 ≤ 40514516959269^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258360607 2500000000 40514516959269 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2358412083/10000000000 : ℝ)^4263 ≤ (746870522191/5000000000000 : ℝ)^3239 := by
    have hnat : (2358412083 : ℕ)^4263*5000000000000^3239 ≤ 746870522191^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358412083 10000000000 746870522191 5000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704907847/5000000000 : ℝ), (1258360607/2500000000 : ℝ), (-2358412083/10000000000 : ℝ)] ![(5568509072829/12500000000000 : ℝ), (40514516959269/100000000000000 : ℝ), (746870522191/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704907847/5000000000 : ℝ)|^4263 ≤ (5568509072829/12500000000000 : ℝ)^3239
        have hw : |(2704907847/5000000000 : ℝ)|=(2704907847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1258360607/2500000000 : ℝ)|^4263 ≤ (40514516959269/100000000000000 : ℝ)^3239
        have hw : |(1258360607/2500000000 : ℝ)|=(1258360607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2358412083/10000000000 : ℝ)|^4263 ≤ (746870522191/5000000000000 : ℝ)^3239
        have hw : |(-2358412083/10000000000 : ℝ)|=(2358412083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s1_3 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537401747/1250000000 : ℝ)*x 0 + (462302297/1250000000 : ℝ)*x 1 + (1247925663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537401747/1250000000 : ℝ)^4263 ≤ (8230498423627/25000000000000 : ℝ)^3239 := by
    have hnat : (537401747 : ℕ)^4263*25000000000000^3239 ≤ 8230498423627^3239*1250000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537401747 1250000000 8230498423627 25000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462302297/1250000000 : ℝ)^4263 ≤ (27005089594033/100000000000000 : ℝ)^3239 := by
    have hnat : (462302297 : ℕ)^4263*100000000000000^3239 ≤ 27005089594033^3239*1250000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462302297 1250000000 27005089594033 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1247925663/2500000000 : ℝ)^4263 ≤ (8014583339823/20000000000000 : ℝ)^3239 := by
    have hnat : (1247925663 : ℕ)^4263*20000000000000^3239 ≤ 8014583339823^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247925663 2500000000 8014583339823 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537401747/1250000000 : ℝ), (462302297/1250000000 : ℝ), (1247925663/2500000000 : ℝ)] ![(8230498423627/25000000000000 : ℝ), (27005089594033/100000000000000 : ℝ), (8014583339823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537401747/1250000000 : ℝ)|^4263 ≤ (8230498423627/25000000000000 : ℝ)^3239
        have hw : |(537401747/1250000000 : ℝ)|=(537401747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(462302297/1250000000 : ℝ)|^4263 ≤ (27005089594033/100000000000000 : ℝ)^3239
        have hw : |(462302297/1250000000 : ℝ)|=(462302297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1247925663/2500000000 : ℝ)|^4263 ≤ (8014583339823/20000000000000 : ℝ)^3239
        have hw : |(1247925663/2500000000 : ℝ)|=(1247925663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s1_4 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-202349747/1000000000 : ℝ)*x 0 + (5041543953/10000000000 : ℝ)*x 1 + (5651817283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202349747/1000000000 : ℝ)^4263 ≤ (1221037870157/10000000000000 : ℝ)^3239 := by
    have hnat : (202349747 : ℕ)^4263*10000000000000^3239 ≤ 1221037870157^3239*1000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202349747 1000000000 1221037870157 10000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5041543953/10000000000 : ℝ)^4263 ≤ (507504554529/1250000000000 : ℝ)^3239 := by
    have hnat : (5041543953 : ℕ)^4263*1250000000000^3239 ≤ 507504554529^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5041543953 10000000000 507504554529 1250000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5651817283/10000000000 : ℝ)^4263 ≤ (47189256928521/100000000000000 : ℝ)^3239 := by
    have hnat : (5651817283 : ℕ)^4263*100000000000000^3239 ≤ 47189256928521^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5651817283 10000000000 47189256928521 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202349747/1000000000 : ℝ), (5041543953/10000000000 : ℝ), (5651817283/10000000000 : ℝ)] ![(1221037870157/10000000000000 : ℝ), (507504554529/1250000000000 : ℝ), (47189256928521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202349747/1000000000 : ℝ)|^4263 ≤ (1221037870157/10000000000000 : ℝ)^3239
        have hw : |(-202349747/1000000000 : ℝ)|=(202349747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5041543953/10000000000 : ℝ)|^4263 ≤ (507504554529/1250000000000 : ℝ)^3239
        have hw : |(5041543953/10000000000 : ℝ)|=(5041543953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5651817283/10000000000 : ℝ)|^4263 ≤ (47189256928521/100000000000000 : ℝ)^3239
        have hw : |(5651817283/10000000000 : ℝ)|=(5651817283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s1_5 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2623879163/5000000000 : ℝ)*x 0 + (-1740036627/10000000000 : ℝ)*x 1 + (5651818057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623879163/5000000000 : ℝ)^4263 ≤ (214000312461/500000000000 : ℝ)^3239 := by
    have hnat : (2623879163 : ℕ)^4263*500000000000^3239 ≤ 214000312461^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623879163 5000000000 214000312461 500000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1740036627/10000000000 : ℝ)^4263 ≤ (10010672061897/100000000000000 : ℝ)^3239 := by
    have hnat : (1740036627 : ℕ)^4263*100000000000000^3239 ≤ 10010672061897^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740036627 10000000000 10010672061897 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5651818057/10000000000 : ℝ)^4263 ≤ (47189265434031/100000000000000 : ℝ)^3239 := by
    have hnat : (5651818057 : ℕ)^4263*100000000000000^3239 ≤ 47189265434031^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5651818057 10000000000 47189265434031 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623879163/5000000000 : ℝ), (-1740036627/10000000000 : ℝ), (5651818057/10000000000 : ℝ)] ![(214000312461/500000000000 : ℝ), (10010672061897/100000000000000 : ℝ), (47189265434031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623879163/5000000000 : ℝ)|^4263 ≤ (214000312461/500000000000 : ℝ)^3239
        have hw : |(2623879163/5000000000 : ℝ)|=(2623879163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1740036627/10000000000 : ℝ)|^4263 ≤ (10010672061897/100000000000000 : ℝ)^3239
        have hw : |(-1740036627/10000000000 : ℝ)|=(1740036627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5651818057/10000000000 : ℝ)|^4263 ≤ (47189265434031/100000000000000 : ℝ)^3239
        have hw : |(5651818057/10000000000 : ℝ)|=(5651818057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s1_6 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049551649/2000000000 : ℝ)*x 0 + (2825908821/5000000000 : ℝ)*x 1 + (-348007469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049551649/2000000000 : ℝ)^4263 ≤ (133750192571/312500000000 : ℝ)^3239 := by
    have hnat : (1049551649 : ℕ)^4263*312500000000^3239 ≤ 133750192571^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049551649 2000000000 133750192571 312500000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2825908821/5000000000 : ℝ)^4263 ≤ (47189260873583/100000000000000 : ℝ)^3239 := by
    have hnat : (2825908821 : ℕ)^4263*100000000000000^3239 ≤ 47189260873583^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825908821 5000000000 47189260873583 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348007469/2000000000 : ℝ)^4263 ≤ (625667343661/6250000000000 : ℝ)^3239 := by
    have hnat : (348007469 : ℕ)^4263*6250000000000^3239 ≤ 625667343661^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348007469 2000000000 625667343661 6250000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049551649/2000000000 : ℝ), (2825908821/5000000000 : ℝ), (-348007469/2000000000 : ℝ)] ![(133750192571/312500000000 : ℝ), (47189260873583/100000000000000 : ℝ), (625667343661/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049551649/2000000000 : ℝ)|^4263 ≤ (133750192571/312500000000 : ℝ)^3239
        have hw : |(1049551649/2000000000 : ℝ)|=(1049551649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2825908821/5000000000 : ℝ)|^4263 ≤ (47189260873583/100000000000000 : ℝ)^3239
        have hw : |(2825908821/5000000000 : ℝ)|=(2825908821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-348007469/2000000000 : ℝ)|^4263 ≤ (625667343661/6250000000000 : ℝ)^3239
        have hw : |(-348007469/2000000000 : ℝ)|=(348007469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s1_7 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537559899/1250000000 : ℝ)*x 0 + (994996613/2000000000 : ℝ)*x 1 + (743090307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537559899/1250000000 : ℝ)^4263 ≤ (32934745930109/100000000000000 : ℝ)^3239 := by
    have hnat : (537559899 : ℕ)^4263*100000000000000^3239 ≤ 32934745930109^3239*1250000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537559899 1250000000 32934745930109 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994996613/2000000000 : ℝ)^4263 ≤ (19948176382551/50000000000000 : ℝ)^3239 := by
    have hnat : (994996613 : ℕ)^4263*50000000000000^3239 ≤ 19948176382551^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994996613 2000000000 19948176382551 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743090307/2000000000 : ℝ)^4263 ≤ (27168901285429/100000000000000 : ℝ)^3239 := by
    have hnat : (743090307 : ℕ)^4263*100000000000000^3239 ≤ 27168901285429^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743090307 2000000000 27168901285429 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537559899/1250000000 : ℝ), (994996613/2000000000 : ℝ), (743090307/2000000000 : ℝ)] ![(32934745930109/100000000000000 : ℝ), (19948176382551/50000000000000 : ℝ), (27168901285429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537559899/1250000000 : ℝ)|^4263 ≤ (32934745930109/100000000000000 : ℝ)^3239
        have hw : |(537559899/1250000000 : ℝ)|=(537559899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994996613/2000000000 : ℝ)|^4263 ≤ (19948176382551/50000000000000 : ℝ)^3239
        have hw : |(994996613/2000000000 : ℝ)|=(994996613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743090307/2000000000 : ℝ)|^4263 ≤ (27168901285429/100000000000000 : ℝ)^3239
        have hw : |(743090307/2000000000 : ℝ)|=(743090307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1303_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13577/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3259/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9881/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13577/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13577/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13577/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13577/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13577/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13577/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (559/50000 : ℝ) ^ (2131/512 : ℝ) ≤ (754052066879/100000000000000000000 : ℝ) := by
    have hpowers : (559/50000 : ℝ)^2131 ≤ (754052066879/100000000000000000000 : ℝ)^512 := by
      have hnat : (559 : ℕ)^2131*100000000000000000000^512 ≤ 754052066879^512*50000^2131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        559 50000 754052066879 100000000000000000000 2131 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (559/50000 : ℝ)) (X := (754052066879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13577/50000 : ℝ) ^ (2131/512 : ℝ) ≤ (440103080129980107/100000000000000000000 : ℝ) := by
    have hpowers : (13577/50000 : ℝ)^2131 ≤ (440103080129980107/100000000000000000000 : ℝ)^512 := by
      have hnat : (13577 : ℕ)^2131*100000000000000000000^512 ≤ 440103080129980107^512*50000^2131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13577 50000 440103080129980107 100000000000000000000 2131 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13577/50000 : ℝ)) (X := (440103080129980107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000754052066879/50000000000000000000 : ℝ) ≤ (10000000036234131/10000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (50000000754052066879/50000000000000000000 : ℝ)^512 ≤ (10000000036234131/10000000000000000 : ℝ)^2131 := by
      have hnat : (50000000754052066879 : ℕ)^512*10000000000000000^2131 ≤ 10000000036234131^2131*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000754052066879 50000000000000000000 10000000036234131 10000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000036234131/10000000000000000 : ℝ)) (X := (50000000754052066879/50000000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50220051917091023493/50000000000000000000 : ℝ) ≤ (10010556425012467/10000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (50220051917091023493/50000000000000000000 : ℝ)^512 ≤ (10010556425012467/10000000000000000 : ℝ)^2131 := by
      have hnat : (50220051917091023493 : ℕ)^512*10000000000000000^2131 ≤ 10010556425012467^2131*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50220051917091023493 50000000000000000000 10010556425012467 10000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010556425012467/10000000000000000 : ℝ)) (X := (50220051917091023493/50000000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50440103080129980107/50000000000000000000 : ℝ) ≤ (10021112813790803/10000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (50440103080129980107/50000000000000000000 : ℝ)^512 ≤ (10021112813790803/10000000000000000 : ℝ)^2131 := by
      have hnat : (50440103080129980107 : ℕ)^512*10000000000000000^2131 ≤ 10021112813790803^2131*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50440103080129980107 50000000000000000000 10021112813790803 10000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021112813790803/10000000000000000 : ℝ)) (X := (50440103080129980107/50000000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(754052066879/100000000000000000000 : ℝ) ≤ ((13016819842904173771/13018000000000000000 : ℝ)+2*(329887149323/81362500000000 : ℝ)*(559/50000 : ℝ))^(2131/512 : ℝ) := by
    rw [show (13016819842904173771/13018000000000000000 : ℝ)+2*(329887149323/81362500000000 : ℝ)*(559/50000 : ℝ)=(10000000036234131/10000000000000000 : ℝ) by norm_num, show 1+2*(754052066879/100000000000000000000 : ℝ)=(50000000754052066879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(440103080129980107/100000000000000000000 : ℝ)+(754052066879/100000000000000000000 : ℝ) ≤ ((13016819842904173771/13018000000000000000 : ℝ)+(329887149323/81362500000000 : ℝ)*((13577/50000 : ℝ)+(559/50000 : ℝ)))^(2131/512 : ℝ) := by
    rw [show (13016819842904173771/13018000000000000000 : ℝ)+(329887149323/81362500000000 : ℝ)*((13577/50000 : ℝ)+(559/50000 : ℝ))=(10010556425012467/10000000000000000 : ℝ) by norm_num, show 1+(440103080129980107/100000000000000000000 : ℝ)+(754052066879/100000000000000000000 : ℝ)=(50220051917091023493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(440103080129980107/100000000000000000000 : ℝ) ≤ ((13016819842904173771/13018000000000000000 : ℝ)+2*(329887149323/81362500000000 : ℝ)*(13577/50000 : ℝ))^(2131/512 : ℝ) := by
    rw [show (13016819842904173771/13018000000000000000 : ℝ)+2*(329887149323/81362500000000 : ℝ)*(13577/50000 : ℝ)=(10021112813790803/10000000000000000 : ℝ) by norm_num, show 1+2*(440103080129980107/100000000000000000000 : ℝ)=(50440103080129980107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13016819842904173771/13018000000000000000 : ℝ)*(X 1 0+X 2 0)+(329887149323/81362500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (559/50000 : ℝ)) (hi := (13577/50000 : ℝ)) (c := (13016819842904173771/13018000000000000000 : ℝ)) (alpha := (329887149323/81362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13016819842904173771/13018000000000000000 : ℝ)*(X 0 1+X 2 1)+(329887149323/81362500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (559/50000 : ℝ)) (hi := (13577/50000 : ℝ)) (c := (13016819842904173771/13018000000000000000 : ℝ)) (alpha := (329887149323/81362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13016819842904173771/13018000000000000000 : ℝ)*(X 0 2+X 1 2)+(329887149323/81362500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (559/50000 : ℝ)) (hi := (13577/50000 : ℝ)) (c := (13016819842904173771/13018000000000000000 : ℝ)) (alpha := (329887149323/81362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1011441997/5000000000 : ℝ)*X 0 0+(1132014131/2000000000 : ℝ)*X 0 1+(314590163/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1081963087/2000000000 : ℝ)*X 1 0+(-58960297/250000000 : ℝ)*X 1 1+(5033442853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2704907847/5000000000 : ℝ)*X 2 0+(1258360607/2500000000 : ℝ)*X 2 1+(-2358412083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((537401747/1250000000 : ℝ)*X 0 0+(462302297/1250000000 : ℝ)*X 0 1+(1247925663/2500000000 : ℝ)*X 0 2+(537401747/1250000000 : ℝ)*X 1 0+(462302297/1250000000 : ℝ)*X 1 1+(1247925663/2500000000 : ℝ)*X 1 2+(537401747/1250000000 : ℝ)*X 2 0+(462302297/1250000000 : ℝ)*X 2 1+(1247925663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-202349747/1000000000 : ℝ)*X 0 0+(5041543953/10000000000 : ℝ)*X 0 1+(5651817283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2623879163/5000000000 : ℝ)*X 1 0+(-1740036627/10000000000 : ℝ)*X 1 1+(5651818057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049551649/2000000000 : ℝ)*X 2 0+(2825908821/5000000000 : ℝ)*X 2 1+(-348007469/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537559899/1250000000 : ℝ)*X 0 0+(994996613/2000000000 : ℝ)*X 0 1+(743090307/2000000000 : ℝ)*X 0 2+(537559899/1250000000 : ℝ)*X 1 0+(994996613/2000000000 : ℝ)*X 1 1+(743090307/2000000000 : ℝ)*X 1 2+(537559899/1250000000 : ℝ)*X 2 0+(994996613/2000000000 : ℝ)*X 2 1+(743090307/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1750390244444195744223137067/650900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2869023/12500000000000 : ℝ)*(base1) + (344902381/100000000000000 : ℝ)*(base19) + (105326259/25000000000000 : ℝ)*(base23) + (89807759/100000000000000 : ℝ)*(upper3) + (29057057/100000000000000 : ℝ)*(upper5) + (1184537043309259/100000000000000 : ℝ)*(major0) + (1184537043309259/100000000000000 : ℝ)*(major1) + (1184537043309259/100000000000000 : ℝ)*(major2) + (398961309498899/25000000000000 : ℝ)*(sp0) + (1595846633398573/100000000000000 : ℝ)*(sp1) + (797923278497959/50000000000000 : ℝ)*(sp2) + (773225907088747/100000000000000 : ℝ)*(sp3) + (881628771/50000000000000 : ℝ)*(sp4) + (544318571/50000000000000 : ℝ)*(sp7) + (386613509339037/50000000000000 : ℝ)*(f.failure) + (797923489150477/50000000000000 : ℝ)*(f.sum) + (8307261673879/8136250000000000000000000000 : ℝ)*base65 + (671881958479965689/1301800000000000000000000000000000 : ℝ)*base67 + (6946549441288034311/1301800000000000000000000000000000 : ℝ)*base70 + (2656635243069434311/1301800000000000000000000000000000 : ℝ)*base72 + (45716267392233/16272500000000000000000000000 : ℝ)*base73 + (32424093615034311/1301800000000000000000000000000000 : ℝ)*base76 + (2592270735723965689/1301800000000000000000000000000000 : ℝ)*base77 + (1272265212916434311/1301800000000000000000000000000000 : ℝ)*base80 + (30018744493411/8136250000000000000000000000 : ℝ)*base82 + (27291149/2500000000000000000000 : ℝ)*base89 + (27291149/2500000000000000000000 : ℝ)*base91 + (27291149/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3747532910532588702811871007/650900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1014387467/100000000000000 : ℝ)*(base19) + (1028803377/100000000000000 : ℝ)*(base23) + (9574717/25000000000000 : ℝ)*(upper2) + (38465491/20000000000000 : ℝ)*(upper3) + (118170199/100000000000000 : ℝ)*(upper5) + (1216277557435361/100000000000000 : ℝ)*(major0) + (1216277557435361/100000000000000 : ℝ)*(major1) + (1216277557435361/100000000000000 : ℝ)*(major2) + (6073577743/100000000000000 : ℝ)*(sp1) + (999221211/20000000000000 : ℝ)*(sp2) + (1638608735343089/100000000000000 : ℝ)*(sp4) + (819300823688939/50000000000000 : ℝ)*(sp5) + (1638602710433657/100000000000000 : ℝ)*(sp6) + (793946187612183/100000000000000 : ℝ)*(sp7) + (793946187612183/100000000000000 : ℝ)*(f.failure) + (1638608735343089/100000000000000 : ℝ)*(f.sum) + (45465067415527/16272500000000000000000000000 : ℝ)*base65 + (5343221067541003669/1301800000000000000000000000000000 : ℝ)*base68 + (1392960762974996331/1301800000000000000000000000000000 : ℝ)*base69 + (4046662518616396331/1301800000000000000000000000000000 : ℝ)*base71 + (347044602381/32545000000000000000000000000 : ℝ)*base74 + (5453071051626596331/1301800000000000000000000000000000 : ℝ)*base75 + (2513007119352796331/1301800000000000000000000000000000 : ℝ)*base77 + (11070604097171603669/1301800000000000000000000000000000 : ℝ)*base80 + (92819164801949/32545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (16170791/5000000000000000000000 : ℝ)*base89 + (16170791/5000000000000000000000 : ℝ)*base91 + (16170791/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1303_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13577/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3259/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9881/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1303_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1303_s2_0 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066545063/10000000000 : ℝ)*x 0 + (5490908771/10000000000 : ℝ)*x 1 + (2587349649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066545063/10000000000 : ℝ)^4263 ≤ (12553407623777/100000000000000 : ℝ)^3239 := by
    have hnat : (2066545063 : ℕ)^4263*100000000000000^3239 ≤ 12553407623777^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066545063 10000000000 12553407623777 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490908771/10000000000 : ℝ)^4263 ≤ (22714519120731/50000000000000 : ℝ)^3239 := by
    have hnat : (5490908771 : ℕ)^4263*50000000000000^3239 ≤ 22714519120731^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490908771 10000000000 22714519120731 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587349649/5000000000 : ℝ)^4263 ≤ (8403510824149/20000000000000 : ℝ)^3239 := by
    have hnat : (2587349649 : ℕ)^4263*20000000000000^3239 ≤ 8403510824149^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587349649 5000000000 8403510824149 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066545063/10000000000 : ℝ), (5490908771/10000000000 : ℝ), (2587349649/5000000000 : ℝ)] ![(12553407623777/100000000000000 : ℝ), (22714519120731/50000000000000 : ℝ), (8403510824149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066545063/10000000000 : ℝ)|^4263 ≤ (12553407623777/100000000000000 : ℝ)^3239
        have hw : |(-2066545063/10000000000 : ℝ)|=(2066545063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490908771/10000000000 : ℝ)|^4263 ≤ (22714519120731/50000000000000 : ℝ)^3239
        have hw : |(5490908771/10000000000 : ℝ)|=(5490908771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587349649/5000000000 : ℝ)|^4263 ≤ (8403510824149/20000000000000 : ℝ)^3239
        have hw : |(2587349649/5000000000 : ℝ)|=(2587349649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s2_1 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684382257/5000000000 : ℝ)*x 0 + (-1115150389/5000000000 : ℝ)*x 1 + (2587349547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684382257/5000000000 : ℝ)^4263 ≤ (22051846384383/50000000000000 : ℝ)^3239 := by
    have hnat : (2684382257 : ℕ)^4263*50000000000000^3239 ≤ 22051846384383^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684382257 5000000000 22051846384383 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115150389/5000000000 : ℝ)^4263 ≤ (173484440903/1250000000000 : ℝ)^3239 := by
    have hnat : (1115150389 : ℕ)^4263*1250000000000^3239 ≤ 173484440903^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115150389 5000000000 173484440903 1250000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587349547/5000000000 : ℝ)^4263 ≤ (21008775970313/50000000000000 : ℝ)^3239 := by
    have hnat : (2587349547 : ℕ)^4263*50000000000000^3239 ≤ 21008775970313^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587349547 5000000000 21008775970313 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684382257/5000000000 : ℝ), (-1115150389/5000000000 : ℝ), (2587349547/5000000000 : ℝ)] ![(22051846384383/50000000000000 : ℝ), (173484440903/1250000000000 : ℝ), (21008775970313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684382257/5000000000 : ℝ)|^4263 ≤ (22051846384383/50000000000000 : ℝ)^3239
        have hw : |(2684382257/5000000000 : ℝ)|=(2684382257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115150389/5000000000 : ℝ)|^4263 ≤ (173484440903/1250000000000 : ℝ)^3239
        have hw : |(-1115150389/5000000000 : ℝ)|=(1115150389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587349547/5000000000 : ℝ)|^4263 ≤ (21008775970313/50000000000000 : ℝ)^3239
        have hw : |(2587349547/5000000000 : ℝ)|=(2587349547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s2_2 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073752839/2000000000 : ℝ)*x 0 + (5174699343/10000000000 : ℝ)*x 1 + (-1115150437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073752839/2000000000 : ℝ)^4263 ≤ (44103689319747/100000000000000 : ℝ)^3239 := by
    have hnat : (1073752839 : ℕ)^4263*100000000000000^3239 ≤ 44103689319747^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073752839 2000000000 44103689319747 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174699343/10000000000 : ℝ)^4263 ≤ (21008777300827/50000000000000 : ℝ)^3239 := by
    have hnat : (5174699343 : ℕ)^4263*50000000000000^3239 ≤ 21008777300827^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174699343 10000000000 21008777300827 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115150437/5000000000 : ℝ)^4263 ≤ (6939378029247/50000000000000 : ℝ)^3239 := by
    have hnat : (1115150437 : ℕ)^4263*50000000000000^3239 ≤ 6939378029247^3239*5000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115150437 5000000000 6939378029247 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073752839/2000000000 : ℝ), (5174699343/10000000000 : ℝ), (-1115150437/5000000000 : ℝ)] ![(44103689319747/100000000000000 : ℝ), (21008777300827/50000000000000 : ℝ), (6939378029247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073752839/2000000000 : ℝ)|^4263 ≤ (44103689319747/100000000000000 : ℝ)^3239
        have hw : |(1073752839/2000000000 : ℝ)|=(1073752839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174699343/10000000000 : ℝ)|^4263 ≤ (21008777300827/50000000000000 : ℝ)^3239
        have hw : |(5174699343/10000000000 : ℝ)|=(5174699343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115150437/5000000000 : ℝ)|^4263 ≤ (6939378029247/50000000000000 : ℝ)^3239
        have hw : |(-1115150437/5000000000 : ℝ)|=(1115150437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s2_3 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865921127/2000000000 : ℝ)*x 0 + (401495167/1000000000 : ℝ)*x 1 + (933515547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865921127/2000000000 : ℝ)^4263 ≤ (259598763077/781250000000 : ℝ)^3239 := by
    have hnat : (865921127 : ℕ)^4263*781250000000^3239 ≤ 259598763077^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865921127 2000000000 259598763077 781250000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401495167/1000000000 : ℝ)^4263 ≤ (30087427777991/100000000000000 : ℝ)^3239 := by
    have hnat : (401495167 : ℕ)^4263*100000000000000^3239 ≤ 30087427777991^3239*1000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401495167 1000000000 30087427777991 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933515547/2000000000 : ℝ)^4263 ≤ (9170982633691/25000000000000 : ℝ)^3239 := by
    have hnat : (933515547 : ℕ)^4263*25000000000000^3239 ≤ 9170982633691^3239*2000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933515547 2000000000 9170982633691 25000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865921127/2000000000 : ℝ), (401495167/1000000000 : ℝ), (933515547/2000000000 : ℝ)] ![(259598763077/781250000000 : ℝ), (30087427777991/100000000000000 : ℝ), (9170982633691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865921127/2000000000 : ℝ)|^4263 ≤ (259598763077/781250000000 : ℝ)^3239
        have hw : |(865921127/2000000000 : ℝ)|=(865921127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401495167/1000000000 : ℝ)|^4263 ≤ (30087427777991/100000000000000 : ℝ)^3239
        have hw : |(401495167/1000000000 : ℝ)|=(401495167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933515547/2000000000 : ℝ)|^4263 ≤ (9170982633691/25000000000000 : ℝ)^3239
        have hw : |(933515547/2000000000 : ℝ)|=(933515547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s2_4 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-516655823/2500000000 : ℝ)*x 0 + (207070859/400000000 : ℝ)*x 1 + (1372204349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516655823/2500000000 : ℝ)^4263 ≤ (1569254134027/12500000000000 : ℝ)^3239 := by
    have hnat : (516655823 : ℕ)^4263*12500000000000^3239 ≤ 1569254134027^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516655823 2500000000 1569254134027 12500000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207070859/400000000 : ℝ)^4263 ≤ (8407940116707/20000000000000 : ℝ)^3239 := by
    have hnat : (207070859 : ℕ)^4263*20000000000000^3239 ≤ 8407940116707^3239*400000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207070859 400000000 8407940116707 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372204349/2500000000 : ℝ)^4263 ≤ (9081253266271/20000000000000 : ℝ)^3239 := by
    have hnat : (1372204349 : ℕ)^4263*20000000000000^3239 ≤ 9081253266271^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372204349 2500000000 9081253266271 20000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516655823/2500000000 : ℝ), (207070859/400000000 : ℝ), (1372204349/2500000000 : ℝ)] ![(1569254134027/12500000000000 : ℝ), (8407940116707/20000000000000 : ℝ), (9081253266271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516655823/2500000000 : ℝ)|^4263 ≤ (1569254134027/12500000000000 : ℝ)^3239
        have hw : |(-516655823/2500000000 : ℝ)|=(516655823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207070859/400000000 : ℝ)|^4263 ≤ (8407940116707/20000000000000 : ℝ)^3239
        have hw : |(207070859/400000000 : ℝ)|=(207070859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372204349/2500000000 : ℝ)|^4263 ≤ (9081253266271/20000000000000 : ℝ)^3239
        have hw : |(1372204349/2500000000 : ℝ)|=(1372204349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s2_5 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287616121/10000000000 : ℝ)*x 0 + (-1916181943/10000000000 : ℝ)*x 1 + (1372204377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287616121/10000000000 : ℝ)^4263 ≤ (43228422021917/100000000000000 : ℝ)^3239 := by
    have hnat : (5287616121 : ℕ)^4263*100000000000000^3239 ≤ 43228422021917^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287616121 10000000000 43228422021917 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916181943/10000000000 : ℝ)^4263 ≤ (11365310414173/100000000000000 : ℝ)^3239 := by
    have hnat : (1916181943 : ℕ)^4263*100000000000000^3239 ≤ 11365310414173^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916181943 10000000000 11365310414173 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372204377/2500000000 : ℝ)^4263 ≤ (5675783443849/12500000000000 : ℝ)^3239 := by
    have hnat : (1372204377 : ℕ)^4263*12500000000000^3239 ≤ 5675783443849^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372204377 2500000000 5675783443849 12500000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287616121/10000000000 : ℝ), (-1916181943/10000000000 : ℝ), (1372204377/2500000000 : ℝ)] ![(43228422021917/100000000000000 : ℝ), (11365310414173/100000000000000 : ℝ), (5675783443849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287616121/10000000000 : ℝ)|^4263 ≤ (43228422021917/100000000000000 : ℝ)^3239
        have hw : |(5287616121/10000000000 : ℝ)|=(5287616121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916181943/10000000000 : ℝ)|^4263 ≤ (11365310414173/100000000000000 : ℝ)^3239
        have hw : |(-1916181943/10000000000 : ℝ)|=(1916181943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372204377/2500000000 : ℝ)|^4263 ≤ (5675783443849/12500000000000 : ℝ)^3239
        have hw : |(1372204377/2500000000 : ℝ)|=(1372204377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s2_6 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287616261/10000000000 : ℝ)*x 0 + (5488817403/10000000000 : ℝ)*x 1 + (-239522737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287616261/10000000000 : ℝ)^4263 ≤ (21614211764161/50000000000000 : ℝ)^3239 := by
    have hnat : (5287616261 : ℕ)^4263*50000000000000^3239 ≤ 21614211764161^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287616261 10000000000 21614211764161 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488817403/10000000000 : ℝ)^4263 ≤ (4540626640757/10000000000000 : ℝ)^3239 := by
    have hnat : (5488817403 : ℕ)^4263*10000000000000^3239 ≤ 4540626640757^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488817403 10000000000 4540626640757 10000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239522737/1250000000 : ℝ)^4263 ≤ (5682655023637/50000000000000 : ℝ)^3239 := by
    have hnat : (239522737 : ℕ)^4263*50000000000000^3239 ≤ 5682655023637^3239*1250000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239522737 1250000000 5682655023637 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287616261/10000000000 : ℝ), (5488817403/10000000000 : ℝ), (-239522737/1250000000 : ℝ)] ![(21614211764161/50000000000000 : ℝ), (4540626640757/10000000000000 : ℝ), (5682655023637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287616261/10000000000 : ℝ)|^4263 ≤ (21614211764161/50000000000000 : ℝ)^3239
        have hw : |(5287616261/10000000000 : ℝ)|=(5287616261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488817403/10000000000 : ℝ)|^4263 ≤ (4540626640757/10000000000000 : ℝ)^3239
        have hw : |(5488817403/10000000000 : ℝ)|=(5488817403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239522737/1250000000 : ℝ)|^4263 ≤ (5682655023637/50000000000000 : ℝ)^3239
        have hw : |(-239522737/1250000000 : ℝ)|=(239522737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1303_s2_7 (p : ℝ) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329766191/10000000000 : ℝ)*x 0 + (1165824771/2500000000 : ℝ)*x 1 + (1004818291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329766191/10000000000 : ℝ)^4263 ≤ (16615131737717/50000000000000 : ℝ)^3239 := by
    have hnat : (4329766191 : ℕ)^4263*50000000000000^3239 ≤ 16615131737717^3239*10000000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329766191 10000000000 16615131737717 50000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165824771/2500000000 : ℝ)^4263 ≤ (36639678565391/100000000000000 : ℝ)^3239 := by
    have hnat : (1165824771 : ℕ)^4263*100000000000000^3239 ≤ 36639678565391^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165824771 2500000000 36639678565391 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004818291/2500000000 : ℝ)^4263 ≤ (30130057932379/100000000000000 : ℝ)^3239 := by
    have hnat : (1004818291 : ℕ)^4263*100000000000000^3239 ≤ 30130057932379^3239*2500000000^4263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004818291 2500000000 30130057932379 100000000000000 4263 3239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4263/1024 : ℝ)) 4263 3239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329766191/10000000000 : ℝ), (1165824771/2500000000 : ℝ), (1004818291/2500000000 : ℝ)] ![(16615131737717/50000000000000 : ℝ), (36639678565391/100000000000000 : ℝ), (30130057932379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329766191/10000000000 : ℝ)|^4263 ≤ (16615131737717/50000000000000 : ℝ)^3239
        have hw : |(4329766191/10000000000 : ℝ)|=(4329766191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165824771/2500000000 : ℝ)|^4263 ≤ (36639678565391/100000000000000 : ℝ)^3239
        have hw : |(1165824771/2500000000 : ℝ)|=(1165824771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004818291/2500000000 : ℝ)|^4263 ≤ (30130057932379/100000000000000 : ℝ)^3239
        have hw : |(1004818291/2500000000 : ℝ)|=(1004818291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1303_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9881/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3259/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1917/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4067/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9881/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3259/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9881/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3259/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9881/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3259/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9881/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3259/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9881/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3259/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9881/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3259/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3259/50000 : ℝ) ^ (2131/512 : ℝ) ≤ (1159349139388989/100000000000000000000 : ℝ) := by
    have hpowers : (3259/50000 : ℝ)^2131 ≤ (1159349139388989/100000000000000000000 : ℝ)^512 := by
      have hnat : (3259 : ℕ)^2131*100000000000000000000^512 ≤ 1159349139388989^512*50000^2131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3259 50000 1159349139388989 100000000000000000000 2131 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3259/50000 : ℝ)) (X := (1159349139388989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9881/50000 : ℝ) ^ (2131/512 : ℝ) ≤ (58632872406213743/50000000000000000000 : ℝ) := by
    have hpowers : (9881/50000 : ℝ)^2131 ≤ (58632872406213743/50000000000000000000 : ℝ)^512 := by
      have hnat : (9881 : ℕ)^2131*50000000000000000000^512 ≤ 58632872406213743^512*50000^2131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9881 50000 58632872406213743 50000000000000000000 2131 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9881/50000 : ℝ)) (X := (58632872406213743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001159349139388989/50000000000000000000 : ℝ) ≤ (10000055709200481/10000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (50001159349139388989/50000000000000000000 : ℝ)^512 ≤ (10000055709200481/10000000000000000 : ℝ)^2131 := by
      have hnat : (50001159349139388989 : ℕ)^512*10000000000000000^2131 ≤ 10000055709200481^2131*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001159349139388989 50000000000000000000 10000055709200481 10000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000055709200481/10000000000000000 : ℝ)) (X := (50001159349139388989/50000000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4004737003758072659/4000000000000000000 : ℝ) ≤ (1000284403521341/1000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (4004737003758072659/4000000000000000000 : ℝ)^512 ≤ (1000284403521341/1000000000000000 : ℝ)^2131 := by
      have hnat : (4004737003758072659 : ℕ)^512*1000000000000000^2131 ≤ 1000284403521341^2131*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4004737003758072659 4000000000000000000 1000284403521341 1000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000284403521341/1000000000000000 : ℝ)) (X := (4004737003758072659/4000000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25058632872406213743/25000000000000000000 : ℝ) ≤ (10005632361226339/10000000000000000 : ℝ) ^ (2131/512 : ℝ) := by
    have hpowers : (25058632872406213743/25000000000000000000 : ℝ)^512 ≤ (10005632361226339/10000000000000000 : ℝ)^2131 := by
      have hnat : (25058632872406213743 : ℕ)^512*10000000000000000^2131 ≤ 10005632361226339^2131*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25058632872406213743 25000000000000000000 10005632361226339 10000000000000000 512 2131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005632361226339/10000000000000000 : ℝ)) (X := (25058632872406213743/25000000000000000000 : ℝ)) (by norm_num) 2131 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1159349139388989/100000000000000000000 : ℝ) ≤ ((1655054864934332849/1655500000000000000 : ℝ)+2*(2788326012929/1324400000000000 : ℝ)*(3259/50000 : ℝ))^(2131/512 : ℝ) := by
    rw [show (1655054864934332849/1655500000000000000 : ℝ)+2*(2788326012929/1324400000000000 : ℝ)*(3259/50000 : ℝ)=(10000055709200481/10000000000000000 : ℝ) by norm_num, show 1+2*(1159349139388989/100000000000000000000 : ℝ)=(50001159349139388989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58632872406213743/50000000000000000000 : ℝ)+(1159349139388989/100000000000000000000 : ℝ) ≤ ((1655054864934332849/1655500000000000000 : ℝ)+(2788326012929/1324400000000000 : ℝ)*((9881/50000 : ℝ)+(3259/50000 : ℝ)))^(2131/512 : ℝ) := by
    rw [show (1655054864934332849/1655500000000000000 : ℝ)+(2788326012929/1324400000000000 : ℝ)*((9881/50000 : ℝ)+(3259/50000 : ℝ))=(1000284403521341/1000000000000000 : ℝ) by norm_num, show 1+(58632872406213743/50000000000000000000 : ℝ)+(1159349139388989/100000000000000000000 : ℝ)=(4004737003758072659/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58632872406213743/50000000000000000000 : ℝ) ≤ ((1655054864934332849/1655500000000000000 : ℝ)+2*(2788326012929/1324400000000000 : ℝ)*(9881/50000 : ℝ))^(2131/512 : ℝ) := by
    rw [show (1655054864934332849/1655500000000000000 : ℝ)+2*(2788326012929/1324400000000000 : ℝ)*(9881/50000 : ℝ)=(10005632361226339/10000000000000000 : ℝ) by norm_num, show 1+2*(58632872406213743/50000000000000000000 : ℝ)=(25058632872406213743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1655054864934332849/1655500000000000000 : ℝ)*(X 1 0+X 2 0)+(2788326012929/1324400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (3259/50000 : ℝ)) (hi := (9881/50000 : ℝ)) (c := (1655054864934332849/1655500000000000000 : ℝ)) (alpha := (2788326012929/1324400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1655054864934332849/1655500000000000000 : ℝ)*(X 0 1+X 2 1)+(2788326012929/1324400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (3259/50000 : ℝ)) (hi := (9881/50000 : ℝ)) (c := (1655054864934332849/1655500000000000000 : ℝ)) (alpha := (2788326012929/1324400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1655054864934332849/1655500000000000000 : ℝ)*(X 0 2+X 1 2)+(2788326012929/1324400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2131/512 : ℝ)) (lo := (3259/50000 : ℝ)) (hi := (9881/50000 : ℝ)) (c := (1655054864934332849/1655500000000000000 : ℝ)) (alpha := (2788326012929/1324400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2066545063/10000000000 : ℝ)*X 0 0+(5490908771/10000000000 : ℝ)*X 0 1+(2587349649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684382257/5000000000 : ℝ)*X 1 0+(-1115150389/5000000000 : ℝ)*X 1 1+(2587349547/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073752839/2000000000 : ℝ)*X 2 0+(5174699343/10000000000 : ℝ)*X 2 1+(-1115150437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865921127/2000000000 : ℝ)*X 0 0+(401495167/1000000000 : ℝ)*X 0 1+(933515547/2000000000 : ℝ)*X 0 2+(865921127/2000000000 : ℝ)*X 1 0+(401495167/1000000000 : ℝ)*X 1 1+(933515547/2000000000 : ℝ)*X 1 2+(865921127/2000000000 : ℝ)*X 2 0+(401495167/1000000000 : ℝ)*X 2 1+(933515547/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-516655823/2500000000 : ℝ)*X 0 0+(207070859/400000000 : ℝ)*X 0 1+(1372204349/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287616121/10000000000 : ℝ)*X 1 0+(-1916181943/10000000000 : ℝ)*X 1 1+(1372204377/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287616261/10000000000 : ℝ)*X 2 0+(5488817403/10000000000 : ℝ)*X 2 1+(-239522737/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4329766191/10000000000 : ℝ)*X 0 0+(1165824771/2500000000 : ℝ)*X 0 1+(1004818291/2500000000 : ℝ)*X 0 2+(4329766191/10000000000 : ℝ)*X 1 0+(1165824771/2500000000 : ℝ)*X 1 1+(1004818291/2500000000 : ℝ)*X 1 2+(4329766191/10000000000 : ℝ)*X 2 0+(1165824771/2500000000 : ℝ)*X 2 1+(1004818291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1303_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4593754427266916672402949/5173437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (266944197/25000000000000 : ℝ)*(base19) + (682835931/100000000000000 : ℝ)*(base23) + (142040587/100000000000000 : ℝ)*(lower2) + (45072013/10000000000000 : ℝ)*(upper3) + (36257541/100000000000000 : ℝ)*(lower4) + (181124323/100000000000000 : ℝ)*(upper5) + (73355592991727/3125000000000 : ℝ)*(major0) + (73355592991727/3125000000000 : ℝ)*(major1) + (73355592991727/3125000000000 : ℝ)*(major2) + (197654108933901/6250000000000 : ℝ)*(sp0) + (790616168791407/25000000000000 : ℝ)*(sp1) + (632493012021297/20000000000000 : ℝ)*(sp2) + (153228034152627/10000000000000 : ℝ)*(sp3) + (1479675437/12500000000000 : ℝ)*(sp7) + (766146089464883/50000000000000 : ℝ)*(f.failure) + (197654108933901/6250000000000 : ℝ)*(f.sum) + (67902951403137/8277500000000000000000000000 : ℝ)*base65 + (60897465609475223/5173437500000000000000000000000 : ℝ)*base67 + (8876780247173549/2586718750000000000000000000000 : ℝ)*base69 + (17530761082192299/2586718750000000000000000000000 : ℝ)*base71 + (457122397041/4138750000000000000000000000 : ℝ)*base73 + (32204024466779799/2586718750000000000000000000000 : ℝ)*base75 + (81749002261541071/10346875000000000000000000000000 : ℝ)*base77 + (85941436710765179/10346875000000000000000000000000 : ℝ)*base80 + (61776095457/2069375000000000000000000000 : ℝ)*base82 + (14541309/2500000000000000000000 : ℝ)*base90 + (14541309/2500000000000000000000 : ℝ)*base92 + (14541309/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30857293568730897178226493/2956250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1000863753/50000000000000 : ℝ)*(base19) + (472219743/20000000000000 : ℝ)*(base23) + (140501491/50000000000000 : ℝ)*(upper3) + (53284607/50000000000000 : ℝ)*(lower4) + (164726759/100000000000000 : ℝ)*(upper5) + (594673393981339/25000000000000 : ℝ)*(major0) + (594673393981339/25000000000000 : ℝ)*(major1) + (594673393981339/25000000000000 : ℝ)*(major2) + (4188897659/20000000000000 : ℝ)*(sp1) + (2569979489/10000000000000 : ℝ)*(sp2) + (100145421210427/3125000000000 : ℝ)*(sp4) + (1602315266258931/50000000000000 : ℝ)*(sp5) + (3204625417840059/100000000000000 : ℝ)*(sp6) + (1552733325184201/100000000000000 : ℝ)*(sp7) + (1552733325184201/100000000000000 : ℝ)*(f.failure) + (100145421210427/3125000000000 : ℝ)*(f.sum) + (10909733937383/8277500000000000000000000000 : ℝ)*base65 + (266981598256568561/41387500000000000000000000000000 : ℝ)*base67 + (206725759505768561/41387500000000000000000000000000 : ℝ)*base69 + (279002223529956061/41387500000000000000000000000000 : ℝ)*base71 + (17325922338009/16555000000000000000000000000 : ℝ)*base74 + (302562088241993561/41387500000000000000000000000000 : ℝ)*base75 + (451772437751368561/41387500000000000000000000000000 : ℝ)*base77 + (96876090741356061/41387500000000000000000000000000 : ℝ)*base79 + (62896897078731/16555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (35239623/5000000000000000000000 : ℝ)*base90 + (35239623/5000000000000000000000 : ℝ)*base92 + (35239623/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1303_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9881/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3259/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1917/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1303_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1303_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1917/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1303_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1303_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1303_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2131/512 : ℝ) ≤ p) (hpb : p ≤ (4263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76596977/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1917/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1303_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
