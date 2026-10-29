-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1433_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:05.905075+00:00
-- url     : https://prove2.me/submissions/b560f457-4b71-4848-be80-71f61d72366b

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
theorem support_rectangle_w1433_s0_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351310313/2000000000 : ℝ)*x 0 + (5958531783/10000000000 : ℝ)*x 1 + (1208038043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351310313/2000000000 : ℝ)^4393 ≤ (2070652749369/20000000000000 : ℝ)^3369 := by
    have hnat : (351310313 : ℕ)^4393*20000000000000^3369 ≤ 2070652749369^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351310313 2000000000 2070652749369 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5958531783/10000000000 : ℝ)^4393 ≤ (407270852133/800000000000 : ℝ)^3369 := by
    have hnat : (5958531783 : ℕ)^4393*800000000000^3369 ≤ 407270852133^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5958531783 10000000000 407270852133 800000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208038043/2500000000 : ℝ)^4393 ≤ (38737879724237/100000000000000 : ℝ)^3369 := by
    have hnat : (1208038043 : ℕ)^4393*100000000000000^3369 ≤ 38737879724237^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208038043 2500000000 38737879724237 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351310313/2000000000 : ℝ), (5958531783/10000000000 : ℝ), (1208038043/2500000000 : ℝ)] ![(2070652749369/20000000000000 : ℝ), (407270852133/800000000000 : ℝ), (38737879724237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351310313/2000000000 : ℝ)|^4393 ≤ (2070652749369/20000000000000 : ℝ)^3369
        have hw : |(-351310313/2000000000 : ℝ)|=(351310313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5958531783/10000000000 : ℝ)|^4393 ≤ (407270852133/800000000000 : ℝ)^3369
        have hw : |(5958531783/10000000000 : ℝ)|=(5958531783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208038043/2500000000 : ℝ)|^4393 ≤ (38737879724237/100000000000000 : ℝ)^3369
        have hw : |(1208038043/2500000000 : ℝ)|=(1208038043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s0_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2745827107/5000000000 : ℝ)*x 0 + (-478532691/2000000000 : ℝ)*x 1 + (4832152611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745827107/5000000000 : ℝ)^4393 ≤ (45770594121851/100000000000000 : ℝ)^3369 := by
    have hnat : (2745827107 : ℕ)^4393*100000000000000^3369 ≤ 45770594121851^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745827107 5000000000 45770594121851 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478532691/2000000000 : ℝ)^4393 ≤ (387288038797/2500000000000 : ℝ)^3369 := by
    have hnat : (478532691 : ℕ)^4393*2500000000000^3369 ≤ 387288038797^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478532691 2000000000 387288038797 2500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4832152611/10000000000 : ℝ)^4393 ≤ (19368942156629/50000000000000 : ℝ)^3369 := by
    have hnat : (4832152611 : ℕ)^4393*50000000000000^3369 ≤ 19368942156629^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832152611 10000000000 19368942156629 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745827107/5000000000 : ℝ), (-478532691/2000000000 : ℝ), (4832152611/10000000000 : ℝ)] ![(45770594121851/100000000000000 : ℝ), (387288038797/2500000000000 : ℝ), (19368942156629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745827107/5000000000 : ℝ)|^4393 ≤ (45770594121851/100000000000000 : ℝ)^3369
        have hw : |(2745827107/5000000000 : ℝ)|=(2745827107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478532691/2000000000 : ℝ)|^4393 ≤ (387288038797/2500000000000 : ℝ)^3369
        have hw : |(-478532691/2000000000 : ℝ)|=(478532691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4832152611/10000000000 : ℝ)|^4393 ≤ (19368942156629/50000000000000 : ℝ)^3369
        have hw : |(4832152611/10000000000 : ℝ)|=(4832152611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s0_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1372913733/2500000000 : ℝ)*x 0 + (1208038099/2500000000 : ℝ)*x 1 + (-2392662797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372913733/2500000000 : ℝ)^4393 ≤ (22885300962483/50000000000000 : ℝ)^3369 := by
    have hnat : (1372913733 : ℕ)^4393*50000000000000^3369 ≤ 22885300962483^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372913733 2500000000 22885300962483 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208038099/2500000000 : ℝ)^4393 ≤ (9684470516447/25000000000000 : ℝ)^3369 := by
    have hnat : (1208038099 : ℕ)^4393*25000000000000^3369 ≤ 9684470516447^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208038099 2500000000 9684470516447 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392662797/10000000000 : ℝ)^4393 ≤ (3098303199339/20000000000000 : ℝ)^3369 := by
    have hnat : (2392662797 : ℕ)^4393*20000000000000^3369 ≤ 3098303199339^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392662797 10000000000 3098303199339 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1372913733/2500000000 : ℝ), (1208038099/2500000000 : ℝ), (-2392662797/10000000000 : ℝ)] ![(22885300962483/50000000000000 : ℝ), (9684470516447/25000000000000 : ℝ), (3098303199339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1372913733/2500000000 : ℝ)|^4393 ≤ (22885300962483/50000000000000 : ℝ)^3369
        have hw : |(1372913733/2500000000 : ℝ)|=(1372913733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208038099/2500000000 : ℝ)|^4393 ≤ (9684470516447/25000000000000 : ℝ)^3369
        have hw : |(1208038099/2500000000 : ℝ)|=(1208038099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2392662797/10000000000 : ℝ)|^4393 ≤ (3098303199339/20000000000000 : ℝ)^3369
        have hw : |(-2392662797/10000000000 : ℝ)|=(2392662797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s0_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165427223/10000000000 : ℝ)*x 0 + (1551630219/5000000000 : ℝ)*x 1 + (1108713829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165427223/10000000000 : ℝ)^4393 ≤ (31919488544371/100000000000000 : ℝ)^3369 := by
    have hnat : (4165427223 : ℕ)^4393*100000000000000^3369 ≤ 31919488544371^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165427223 10000000000 31919488544371 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551630219/5000000000 : ℝ)^4393 ≤ (4348980984811/20000000000000 : ℝ)^3369 := by
    have hnat : (1551630219 : ℕ)^4393*20000000000000^3369 ≤ 4348980984811^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551630219 5000000000 4348980984811 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108713829/2000000000 : ℝ)^4393 ≤ (11583901627457/25000000000000 : ℝ)^3369 := by
    have hnat : (1108713829 : ℕ)^4393*25000000000000^3369 ≤ 11583901627457^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108713829 2000000000 11583901627457 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165427223/10000000000 : ℝ), (1551630219/5000000000 : ℝ), (1108713829/2000000000 : ℝ)] ![(31919488544371/100000000000000 : ℝ), (4348980984811/20000000000000 : ℝ), (11583901627457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165427223/10000000000 : ℝ)|^4393 ≤ (31919488544371/100000000000000 : ℝ)^3369
        have hw : |(4165427223/10000000000 : ℝ)|=(4165427223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551630219/5000000000 : ℝ)|^4393 ≤ (4348980984811/20000000000000 : ℝ)^3369
        have hw : |(1551630219/5000000000 : ℝ)|=(1551630219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108713829/2000000000 : ℝ)|^4393 ≤ (11583901627457/25000000000000 : ℝ)^3369
        have hw : |(1108713829/2000000000 : ℝ)|=(1108713829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s0_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-880274673/5000000000 : ℝ)*x 0 + (19443851/40000000 : ℝ)*x 1 + (1185738557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880274673/5000000000 : ℝ)^4393 ≤ (5191999814251/50000000000000 : ℝ)^3369 := by
    have hnat : (880274673 : ℕ)^4393*50000000000000^3369 ≤ 5191999814251^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880274673 5000000000 5191999814251 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19443851/40000000 : ℝ)^4393 ≤ (39039319254813/100000000000000 : ℝ)^3369 := by
    have hnat : (19443851 : ℕ)^4393*100000000000000^3369 ≤ 39039319254813^3369*40000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19443851 40000000 39039319254813 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1185738557/2000000000 : ℝ)^4393 ≤ (50576681107681/100000000000000 : ℝ)^3369 := by
    have hnat : (1185738557 : ℕ)^4393*100000000000000^3369 ≤ 50576681107681^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185738557 2000000000 50576681107681 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-880274673/5000000000 : ℝ), (19443851/40000000 : ℝ), (1185738557/2000000000 : ℝ)] ![(5191999814251/50000000000000 : ℝ), (39039319254813/100000000000000 : ℝ), (50576681107681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-880274673/5000000000 : ℝ)|^4393 ≤ (5191999814251/50000000000000 : ℝ)^3369
        have hw : |(-880274673/5000000000 : ℝ)|=(880274673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19443851/40000000 : ℝ)|^4393 ≤ (39039319254813/100000000000000 : ℝ)^3369
        have hw : |(19443851/40000000 : ℝ)|=(19443851/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1185738557/2000000000 : ℝ)|^4393 ≤ (50576681107681/100000000000000 : ℝ)^3369
        have hw : |(1185738557/2000000000 : ℝ)|=(1185738557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s0_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036840569/2000000000 : ℝ)*x 0 + (-648061237/5000000000 : ℝ)*x 1 + (5928692857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036840569/2000000000 : ℝ)^4393 ≤ (42458066715627/100000000000000 : ℝ)^3369 := by
    have hnat : (1036840569 : ℕ)^4393*100000000000000^3369 ≤ 42458066715627^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036840569 2000000000 42458066715627 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648061237/5000000000 : ℝ)^4393 ≤ (3482625681009/50000000000000 : ℝ)^3369 := by
    have hnat : (648061237 : ℕ)^4393*50000000000000^3369 ≤ 3482625681009^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648061237 5000000000 3482625681009 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5928692857/10000000000 : ℝ)^4393 ≤ (50576681908591/100000000000000 : ℝ)^3369 := by
    have hnat : (5928692857 : ℕ)^4393*100000000000000^3369 ≤ 50576681908591^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5928692857 10000000000 50576681908591 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036840569/2000000000 : ℝ), (-648061237/5000000000 : ℝ), (5928692857/10000000000 : ℝ)] ![(42458066715627/100000000000000 : ℝ), (3482625681009/50000000000000 : ℝ), (50576681908591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036840569/2000000000 : ℝ)|^4393 ≤ (42458066715627/100000000000000 : ℝ)^3369
        have hw : |(1036840569/2000000000 : ℝ)|=(1036840569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-648061237/5000000000 : ℝ)|^4393 ≤ (3482625681009/50000000000000 : ℝ)^3369
        have hw : |(-648061237/5000000000 : ℝ)|=(648061237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5928692857/10000000000 : ℝ)|^4393 ≤ (50576681908591/100000000000000 : ℝ)^3369
        have hw : |(5928692857/10000000000 : ℝ)|=(5928692857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s0_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296050717/2500000000 : ℝ)*x 0 + (2964346349/5000000000 : ℝ)*x 1 + (-1296122691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296050717/2500000000 : ℝ)^4393 ≤ (1326814592539/3125000000000 : ℝ)^3369 := by
    have hnat : (1296050717 : ℕ)^4393*3125000000000^3369 ≤ 1326814592539^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296050717 2500000000 1326814592539 3125000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2964346349/5000000000 : ℝ)^4393 ≤ (25288340069957/50000000000000 : ℝ)^3369 := by
    have hnat : (2964346349 : ℕ)^4393*50000000000000^3369 ≤ 25288340069957^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2964346349 5000000000 25288340069957 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296122691/10000000000 : ℝ)^4393 ≤ (6965252882603/100000000000000 : ℝ)^3369 := by
    have hnat : (1296122691 : ℕ)^4393*100000000000000^3369 ≤ 6965252882603^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296122691 10000000000 6965252882603 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296050717/2500000000 : ℝ), (2964346349/5000000000 : ℝ), (-1296122691/10000000000 : ℝ)] ![(1326814592539/3125000000000 : ℝ), (25288340069957/50000000000000 : ℝ), (6965252882603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296050717/2500000000 : ℝ)|^4393 ≤ (1326814592539/3125000000000 : ℝ)^3369
        have hw : |(1296050717/2500000000 : ℝ)|=(1296050717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2964346349/5000000000 : ℝ)|^4393 ≤ (25288340069957/50000000000000 : ℝ)^3369
        have hw : |(2964346349/5000000000 : ℝ)|=(2964346349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1296122691/10000000000 : ℝ)|^4393 ≤ (6965252882603/100000000000000 : ℝ)^3369
        have hw : |(-1296122691/10000000000 : ℝ)|=(1296122691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s0_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174091031/10000000000 : ℝ)*x 0 + (5481150327/10000000000 : ℝ)*x 1 + (1583953819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174091031/10000000000 : ℝ)^4393 ≤ (6401217098033/20000000000000 : ℝ)^3369 := by
    have hnat : (4174091031 : ℕ)^4393*20000000000000^3369 ≤ 6401217098033^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174091031 10000000000 6401217098033 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481150327/10000000000 : ℝ)^4393 ≤ (45656472671087/100000000000000 : ℝ)^3369 := by
    have hnat : (5481150327 : ℕ)^4393*100000000000000^3369 ≤ 45656472671087^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481150327 10000000000 45656472671087 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583953819/5000000000 : ℝ)^4393 ≤ (22337441828739/100000000000000 : ℝ)^3369 := by
    have hnat : (1583953819 : ℕ)^4393*100000000000000^3369 ≤ 22337441828739^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583953819 5000000000 22337441828739 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174091031/10000000000 : ℝ), (5481150327/10000000000 : ℝ), (1583953819/5000000000 : ℝ)] ![(6401217098033/20000000000000 : ℝ), (45656472671087/100000000000000 : ℝ), (22337441828739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174091031/10000000000 : ℝ)|^4393 ≤ (6401217098033/20000000000000 : ℝ)^3369
        have hw : |(4174091031/10000000000 : ℝ)|=(4174091031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481150327/10000000000 : ℝ)|^4393 ≤ (45656472671087/100000000000000 : ℝ)^3369
        have hw : |(5481150327/10000000000 : ℝ)|=(5481150327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1583953819/5000000000 : ℝ)|^4393 ≤ (22337441828739/100000000000000 : ℝ)^3369
        have hw : |(1583953819/5000000000 : ℝ)|=(1583953819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (519/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2623/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (549/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^549 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^549*1^128 ≤ 0^128*1^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (549/128 : ℝ) ≤ (78572473087443773/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^549 ≤ (78572473087443773/4000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^549*4000000000000000000^128 ≤ 78572473087443773^128*5^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 78572473087443773 4000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (78572473087443773/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^549 := by
      have hnat : (1 : ℕ)^128*1^549 ≤ 1^549*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (4078572473087443773/4000000000000000000 : ℝ) ≤ (10045457164106101/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (4078572473087443773/4000000000000000000 : ℝ)^128 ≤ (10045457164106101/10000000000000000 : ℝ)^549 := by
      have hnat : (4078572473087443773 : ℕ)^128*10000000000000000^549 ≤ 10045457164106101^549*4000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4078572473087443773 4000000000000000000 10045457164106101 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045457164106101/10000000000000000 : ℝ)) (X := (4078572473087443773/4000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (2078572473087443773/2000000000000000000 : ℝ) ≤ (5045457164106101/5000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (2078572473087443773/2000000000000000000 : ℝ)^128 ≤ (5045457164106101/5000000000000000 : ℝ)^549 := by
      have hnat : (2078572473087443773 : ℕ)^128*5000000000000000^549 ≤ 5045457164106101^549*2000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2078572473087443773 2000000000000000000 5045457164106101 5000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045457164106101/5000000000000000 : ℝ)) (X := (2078572473087443773/2000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45457164106101/4000000000000000 : ℝ)*(0 : ℝ))^(549/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(45457164106101/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78572473087443773/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45457164106101/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(549/128 : ℝ) := by
    rw [show (1 : ℝ)+(45457164106101/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045457164106101/10000000000000000 : ℝ) by norm_num, show 1+(78572473087443773/4000000000000000000 : ℝ)+(0 : ℝ)=(4078572473087443773/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78572473087443773/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45457164106101/4000000000000000 : ℝ)*(2/5 : ℝ))^(549/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(45457164106101/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045457164106101/5000000000000000 : ℝ) by norm_num, show 1+2*(78572473087443773/4000000000000000000 : ℝ)=(2078572473087443773/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45457164106101/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45457164106101/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45457164106101/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45457164106101/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45457164106101/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45457164106101/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-351310313/2000000000 : ℝ)*X 0 0+(5958531783/10000000000 : ℝ)*X 0 1+(1208038043/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2745827107/5000000000 : ℝ)*X 1 0+(-478532691/2000000000 : ℝ)*X 1 1+(4832152611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1372913733/2500000000 : ℝ)*X 2 0+(1208038099/2500000000 : ℝ)*X 2 1+(-2392662797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4165427223/10000000000 : ℝ)*X 0 0+(1551630219/5000000000 : ℝ)*X 0 1+(1108713829/2000000000 : ℝ)*X 0 2+(4165427223/10000000000 : ℝ)*X 1 0+(1551630219/5000000000 : ℝ)*X 1 1+(1108713829/2000000000 : ℝ)*X 1 2+(4165427223/10000000000 : ℝ)*X 2 0+(1551630219/5000000000 : ℝ)*X 2 1+(1108713829/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-880274673/5000000000 : ℝ)*X 0 0+(19443851/40000000 : ℝ)*X 0 1+(1185738557/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036840569/2000000000 : ℝ)*X 1 0+(-648061237/5000000000 : ℝ)*X 1 1+(5928692857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296050717/2500000000 : ℝ)*X 2 0+(2964346349/5000000000 : ℝ)*X 2 1+(-1296122691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4174091031/10000000000 : ℝ)*X 0 0+(5481150327/10000000000 : ℝ)*X 0 1+(1583953819/5000000000 : ℝ)*X 0 2+(4174091031/10000000000 : ℝ)*X 1 0+(5481150327/10000000000 : ℝ)*X 1 1+(1583953819/5000000000 : ℝ)*X 1 2+(4174091031/10000000000 : ℝ)*X 2 0+(5481150327/10000000000 : ℝ)*X 2 1+(1583953819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (689999212078864341215433/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15036289/1562500000000 : ℝ)*(base19) + (965204969/100000000000000 : ℝ)*(base23) + (78714751/100000000000000 : ℝ)*(upper3) + (6216153/10000000000000 : ℝ)*(upper4) + (189337623/100000000000000 : ℝ)*(upper5) + (648797489034711/100000000000000 : ℝ)*(major0) + (648797489034711/100000000000000 : ℝ)*(major1) + (648797489034711/100000000000000 : ℝ)*(major2) + (887802978263957/100000000000000 : ℝ)*(sp0) + (887806188824411/100000000000000 : ℝ)*(sp1) + (443903092970969/50000000000000 : ℝ)*(sp2) + (16391441106047/4000000000000 : ℝ)*(sp3) + (83457659/2000000000000 : ℝ)*(sp4) + (336854293/20000000000000 : ℝ)*(sp7) + (5122346399033/1250000000000 : ℝ)*(f.failure) + (887807151146907/100000000000000 : ℝ)*(f.sum) + (420031131128189/200000000000000000000000000000 : ℝ)*base66 + (2314472938528189/400000000000000000000000000000 : ℝ)*base68 + (3556673516271811/400000000000000000000000000000 : ℝ)*base69 + (1795150481728189/400000000000000000000000000000 : ℝ)*base72 + (672323064128189/200000000000000000000000000000 : ℝ)*base74 + (3671550809471811/400000000000000000000000000000 : ℝ)*base75 + (398798586528189/400000000000000000000000000000 : ℝ)*base78 + (1199276814671811/400000000000000000000000000000 : ℝ)*base79 + (1214550784071811/200000000000000000000000000000 : ℝ)*base81 + (483189/125000000000000000000 : ℝ)*base90 + (483189/125000000000000000000 : ℝ)*base92 + (483189/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91141735674084183054249/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411515093/100000000000000 : ℝ)*(base19) + (207182341/50000000000000 : ℝ)*(base23) + (21666089/25000000000000 : ℝ)*(base32) + (68342571/100000000000000 : ℝ)*(upper3) + (20247523/100000000000000 : ℝ)*(upper5) + (171107435741783/25000000000000 : ℝ)*(major0) + (171107435741783/25000000000000 : ℝ)*(major1) + (171107435741783/25000000000000 : ℝ)*(major2) + (241534997/25000000000000 : ℝ)*(sp1) + (944124103/100000000000000 : ℝ)*(sp2) + (936565985259227/100000000000000 : ℝ)*(sp4) + (468282303802073/50000000000000 : ℝ)*(sp5) + (468282313385221/50000000000000 : ℝ)*(sp6) + (216146676624761/50000000000000 : ℝ)*(sp7) + (216146719956939/50000000000000 : ℝ)*(f.failure) + (936565985259227/100000000000000 : ℝ)*(f.sum) + (24026968918083/50000000000000000000000000000 : ℝ)*base65 + (205154256518083/100000000000000000000000000000 : ℝ)*base67 + (271799572181917/100000000000000000000000000000 : ℝ)*base70 + (38888852518083/100000000000000000000000000000 : ℝ)*base71 + (8225846581917/50000000000000000000000000000 : ℝ)*base74 + (112791231681917/100000000000000000000000000000 : ℝ)*base76 + (252406032481917/100000000000000000000000000000 : ℝ)*base78 + (235190351118083/100000000000000000000000000000 : ℝ)*base79 + (135489625231917/50000000000000000000000000000 : ℝ)*base82 + (4322287/5000000000000000000000 : ℝ)*base90 + (4322287/5000000000000000000000 : ℝ)*base92 + (4322287/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1433_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (519/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2623/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1433_s1_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1928343967/10000000000 : ℝ)*x 0 + (5603616903/10000000000 : ℝ)*x 1 + (5076927777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928343967/10000000000 : ℝ)^4393 ≤ (2923196054699/25000000000000 : ℝ)^3369 := by
    have hnat : (1928343967 : ℕ)^4393*25000000000000^3369 ≤ 2923196054699^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928343967 10000000000 2923196054699 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5603616903/10000000000 : ℝ)^4393 ≤ (5873892507561/12500000000000 : ℝ)^3369 := by
    have hnat : (5603616903 : ℕ)^4393*12500000000000^3369 ≤ 5873892507561^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603616903 10000000000 5873892507561 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076927777/10000000000 : ℝ)^4393 ≤ (8263215140997/20000000000000 : ℝ)^3369 := by
    have hnat : (5076927777 : ℕ)^4393*20000000000000^3369 ≤ 8263215140997^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076927777 10000000000 8263215140997 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1928343967/10000000000 : ℝ), (5603616903/10000000000 : ℝ), (5076927777/10000000000 : ℝ)] ![(2923196054699/25000000000000 : ℝ), (5873892507561/12500000000000 : ℝ), (8263215140997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1928343967/10000000000 : ℝ)|^4393 ≤ (2923196054699/25000000000000 : ℝ)^3369
        have hw : |(-1928343967/10000000000 : ℝ)|=(1928343967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5603616903/10000000000 : ℝ)|^4393 ≤ (5873892507561/12500000000000 : ℝ)^3369
        have hw : |(5603616903/10000000000 : ℝ)|=(5603616903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076927777/10000000000 : ℝ)|^4393 ≤ (8263215140997/20000000000000 : ℝ)^3369
        have hw : |(5076927777/10000000000 : ℝ)|=(5076927777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s1_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396406121/10000000000 : ℝ)*x 0 + (-1103672053/5000000000 : ℝ)*x 1 + (2538464671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396406121/10000000000 : ℝ)^4393 ≤ (22369095933459/50000000000000 : ℝ)^3369 := by
    have hnat : (5396406121 : ℕ)^4393*50000000000000^3369 ≤ 22369095933459^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396406121 10000000000 22369095933459 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103672053/5000000000 : ℝ)^4393 ≤ (2789143161207/20000000000000 : ℝ)^3369 := by
    have hnat : (1103672053 : ℕ)^4393*20000000000000^3369 ≤ 2789143161207^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103672053 5000000000 2789143161207 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538464671/5000000000 : ℝ)^4393 ≤ (41316092312041/100000000000000 : ℝ)^3369 := by
    have hnat : (2538464671 : ℕ)^4393*100000000000000^3369 ≤ 41316092312041^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538464671 5000000000 41316092312041 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396406121/10000000000 : ℝ), (-1103672053/5000000000 : ℝ), (2538464671/5000000000 : ℝ)] ![(22369095933459/50000000000000 : ℝ), (2789143161207/20000000000000 : ℝ), (41316092312041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396406121/10000000000 : ℝ)|^4393 ≤ (22369095933459/50000000000000 : ℝ)^3369
        have hw : |(5396406121/10000000000 : ℝ)|=(5396406121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103672053/5000000000 : ℝ)|^4393 ≤ (2789143161207/20000000000000 : ℝ)^3369
        have hw : |(-1103672053/5000000000 : ℝ)|=(1103672053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538464671/5000000000 : ℝ)|^4393 ≤ (41316092312041/100000000000000 : ℝ)^3369
        have hw : |(2538464671/5000000000 : ℝ)|=(2538464671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s1_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53964073/100000000 : ℝ)*x 0 + (126923201/250000000 : ℝ)*x 1 + (-551836059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53964073/100000000 : ℝ)^4393 ≤ (5592275576519/12500000000000 : ℝ)^3369 := by
    have hnat : (53964073 : ℕ)^4393*12500000000000^3369 ≤ 5592275576519^3369*100000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53964073 100000000 5592275576519 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126923201/250000000 : ℝ)^4393 ≤ (41316078495819/100000000000000 : ℝ)^3369 := by
    have hnat : (126923201 : ℕ)^4393*100000000000000^3369 ≤ 41316078495819^3369*250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126923201 250000000 41316078495819 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551836059/2500000000 : ℝ)^4393 ≤ (6972858438499/50000000000000 : ℝ)^3369 := by
    have hnat : (551836059 : ℕ)^4393*50000000000000^3369 ≤ 6972858438499^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551836059 2500000000 6972858438499 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53964073/100000000 : ℝ), (126923201/250000000 : ℝ), (-551836059/2500000000 : ℝ)] ![(5592275576519/12500000000000 : ℝ), (41316078495819/100000000000000 : ℝ), (6972858438499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53964073/100000000 : ℝ)|^4393 ≤ (5592275576519/12500000000000 : ℝ)^3369
        have hw : |(53964073/100000000 : ℝ)|=(53964073/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126923201/250000000 : ℝ)|^4393 ≤ (41316078495819/100000000000000 : ℝ)^3369
        have hw : |(126923201/250000000 : ℝ)|=(126923201/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-551836059/2500000000 : ℝ)|^4393 ≤ (6972858438499/50000000000000 : ℝ)^3369
        have hw : |(-551836059/2500000000 : ℝ)|=(551836059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s1_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275913249/10000000000 : ℝ)*x 0 + (233706169/625000000 : ℝ)*x 1 + (4880370739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275913249/10000000000 : ℝ)^4393 ≤ (33027898567669/100000000000000 : ℝ)^3369 := by
    have hnat : (4275913249 : ℕ)^4393*100000000000000^3369 ≤ 33027898567669^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275913249 10000000000 33027898567669 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233706169/625000000 : ℝ)^4393 ≤ (6932353394731/25000000000000 : ℝ)^3369 := by
    have hnat : (233706169 : ℕ)^4393*25000000000000^3369 ≤ 6932353394731^3369*625000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233706169 625000000 6932353394731 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880370739/10000000000 : ℝ)^4393 ≤ (39242687840311/100000000000000 : ℝ)^3369 := by
    have hnat : (4880370739 : ℕ)^4393*100000000000000^3369 ≤ 39242687840311^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880370739 10000000000 39242687840311 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275913249/10000000000 : ℝ), (233706169/625000000 : ℝ), (4880370739/10000000000 : ℝ)] ![(33027898567669/100000000000000 : ℝ), (6932353394731/25000000000000 : ℝ), (39242687840311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275913249/10000000000 : ℝ)|^4393 ≤ (33027898567669/100000000000000 : ℝ)^3369
        have hw : |(4275913249/10000000000 : ℝ)|=(4275913249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(233706169/625000000 : ℝ)|^4393 ≤ (6932353394731/25000000000000 : ℝ)^3369
        have hw : |(233706169/625000000 : ℝ)|=(233706169/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880370739/10000000000 : ℝ)|^4393 ≤ (39242687840311/100000000000000 : ℝ)^3369
        have hw : |(4880370739/10000000000 : ℝ)|=(4880370739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s1_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-964368199/5000000000 : ℝ)*x 0 + (5083084421/10000000000 : ℝ)*x 1 + (5597356293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964368199/5000000000 : ℝ)^4393 ≤ (11695887137247/100000000000000 : ℝ)^3369 := by
    have hnat : (964368199 : ℕ)^4393*100000000000000^3369 ≤ 11695887137247^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964368199 5000000000 11695887137247 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083084421/10000000000 : ℝ)^4393 ≤ (41381419194233/100000000000000 : ℝ)^3369 := by
    have hnat : (5083084421 : ℕ)^4393*100000000000000^3369 ≤ 41381419194233^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083084421 10000000000 41381419194233 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5597356293/10000000000 : ℝ)^4393 ≤ (11730673414657/25000000000000 : ℝ)^3369 := by
    have hnat : (5597356293 : ℕ)^4393*25000000000000^3369 ≤ 11730673414657^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597356293 10000000000 11730673414657 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-964368199/5000000000 : ℝ), (5083084421/10000000000 : ℝ), (5597356293/10000000000 : ℝ)] ![(11695887137247/100000000000000 : ℝ), (41381419194233/100000000000000 : ℝ), (11730673414657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-964368199/5000000000 : ℝ)|^4393 ≤ (11695887137247/100000000000000 : ℝ)^3369
        have hw : |(-964368199/5000000000 : ℝ)|=(964368199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083084421/10000000000 : ℝ)|^4393 ≤ (41381419194233/100000000000000 : ℝ)^3369
        have hw : |(5083084421/10000000000 : ℝ)|=(5083084421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5597356293/10000000000 : ℝ)|^4393 ≤ (11730673414657/25000000000000 : ℝ)^3369
        have hw : |(5597356293/10000000000 : ℝ)|=(5597356293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s1_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258756499/10000000000 : ℝ)*x 0 + (-67476659/400000000 : ℝ)*x 1 + (5597356311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258756499/10000000000 : ℝ)^4393 ≤ (2703498364697/6250000000000 : ℝ)^3369 := by
    have hnat : (5258756499 : ℕ)^4393*6250000000000^3369 ≤ 2703498364697^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258756499 10000000000 2703498364697 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67476659/400000000 : ℝ)^4393 ≤ (9821332298607/100000000000000 : ℝ)^3369 := by
    have hnat : (67476659 : ℕ)^4393*100000000000000^3369 ≤ 9821332298607^3369*400000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67476659 400000000 9821332298607 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5597356311/10000000000 : ℝ)^4393 ≤ (46922693855387/100000000000000 : ℝ)^3369 := by
    have hnat : (5597356311 : ℕ)^4393*100000000000000^3369 ≤ 46922693855387^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597356311 10000000000 46922693855387 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258756499/10000000000 : ℝ), (-67476659/400000000 : ℝ), (5597356311/10000000000 : ℝ)] ![(2703498364697/6250000000000 : ℝ), (9821332298607/100000000000000 : ℝ), (46922693855387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258756499/10000000000 : ℝ)|^4393 ≤ (2703498364697/6250000000000 : ℝ)^3369
        have hw : |(5258756499/10000000000 : ℝ)|=(5258756499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67476659/400000000 : ℝ)|^4393 ≤ (9821332298607/100000000000000 : ℝ)^3369
        have hw : |(-67476659/400000000 : ℝ)|=(67476659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5597356311/10000000000 : ℝ)|^4393 ≤ (46922693855387/100000000000000 : ℝ)^3369
        have hw : |(5597356311/10000000000 : ℝ)|=(5597356311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s1_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629378221/5000000000 : ℝ)*x 0 + (349834767/625000000 : ℝ)*x 1 + (-1686916611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629378221/5000000000 : ℝ)^4393 ≤ (43255973223791/100000000000000 : ℝ)^3369 := by
    have hnat : (2629378221 : ℕ)^4393*100000000000000^3369 ≤ 43255973223791^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629378221 5000000000 43255973223791 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349834767/625000000 : ℝ)^4393 ≤ (46922693429077/100000000000000 : ℝ)^3369 := by
    have hnat : (349834767 : ℕ)^4393*100000000000000^3369 ≤ 46922693429077^3369*625000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349834767 625000000 46922693429077 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1686916611/10000000000 : ℝ)^4393 ≤ (9821333331073/100000000000000 : ℝ)^3369 := by
    have hnat : (1686916611 : ℕ)^4393*100000000000000^3369 ≤ 9821333331073^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686916611 10000000000 9821333331073 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629378221/5000000000 : ℝ), (349834767/625000000 : ℝ), (-1686916611/10000000000 : ℝ)] ![(43255973223791/100000000000000 : ℝ), (46922693429077/100000000000000 : ℝ), (9821333331073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629378221/5000000000 : ℝ)|^4393 ≤ (43255973223791/100000000000000 : ℝ)^3369
        have hw : |(2629378221/5000000000 : ℝ)|=(2629378221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349834767/625000000 : ℝ)|^4393 ≤ (46922693429077/100000000000000 : ℝ)^3369
        have hw : |(349834767/625000000 : ℝ)|=(349834767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1686916611/10000000000 : ℝ)|^4393 ≤ (9821333331073/100000000000000 : ℝ)^3369
        have hw : |(-1686916611/10000000000 : ℝ)|=(1686916611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s1_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4276764233/10000000000 : ℝ)*x 0 + (2433516781/5000000000 : ℝ)*x 1 + (3752860511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276764233/10000000000 : ℝ)^4393 ≤ (16518234934647/50000000000000 : ℝ)^3369 := by
    have hnat : (4276764233 : ℕ)^4393*50000000000000^3369 ≤ 16518234934647^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276764233 10000000000 16518234934647 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2433516781/5000000000 : ℝ)^4393 ≤ (39102906398361/100000000000000 : ℝ)^3369 := by
    have hnat : (2433516781 : ℕ)^4393*100000000000000^3369 ≤ 39102906398361^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2433516781 5000000000 39102906398361 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3752860511/10000000000 : ℝ)^4393 ≤ (27860623715381/100000000000000 : ℝ)^3369 := by
    have hnat : (3752860511 : ℕ)^4393*100000000000000^3369 ≤ 27860623715381^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752860511 10000000000 27860623715381 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276764233/10000000000 : ℝ), (2433516781/5000000000 : ℝ), (3752860511/10000000000 : ℝ)] ![(16518234934647/50000000000000 : ℝ), (39102906398361/100000000000000 : ℝ), (27860623715381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276764233/10000000000 : ℝ)|^4393 ≤ (16518234934647/50000000000000 : ℝ)^3369
        have hw : |(4276764233/10000000000 : ℝ)|=(4276764233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2433516781/5000000000 : ℝ)|^4393 ≤ (39102906398361/100000000000000 : ℝ)^3369
        have hw : |(2433516781/5000000000 : ℝ)|=(2433516781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3752860511/10000000000 : ℝ)|^4393 ≤ (27860623715381/100000000000000 : ℝ)^3369
        have hw : |(3752860511/10000000000 : ℝ)|=(3752860511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2623/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1537/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (941/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2623/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (519/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2623/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (519/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2623/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (519/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2623/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (519/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2623/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (519/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2623/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (519/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (519/25000 : ℝ) ^ (549/128 : ℝ) ≤ (3030071884283/50000000000000000000 : ℝ) := by
    have hpowers : (519/25000 : ℝ)^549 ≤ (3030071884283/50000000000000000000 : ℝ)^128 := by
      have hnat : (519 : ℕ)^549*50000000000000000000^128 ≤ 3030071884283^128*25000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        519 25000 3030071884283 50000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (519/25000 : ℝ)) (X := (3030071884283/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2623/10000 : ℝ) ^ (549/128 : ℝ) ≤ (160753170645978643/50000000000000000000 : ℝ) := by
    have hpowers : (2623/10000 : ℝ)^549 ≤ (160753170645978643/50000000000000000000 : ℝ)^128 := by
      have hnat : (2623 : ℕ)^549*50000000000000000000^128 ≤ 160753170645978643^128*10000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2623 10000 160753170645978643 50000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2623/10000 : ℝ)) (X := (160753170645978643/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003030071884283/25000000000000000000 : ℝ) ≤ (5000000141292963/5000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (25000003030071884283/25000000000000000000 : ℝ)^128 ≤ (5000000141292963/5000000000000000 : ℝ)^549 := by
      have hnat : (25000003030071884283 : ℕ)^128*5000000000000000^549 ≤ 5000000141292963^549*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003030071884283 25000000000000000000 5000000141292963 5000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000141292963/5000000000000000 : ℝ)) (X := (25000003030071884283/25000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25080378100358931463/25000000000000000000 : ℝ) ≤ (625467929768453/625000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (25080378100358931463/25000000000000000000 : ℝ)^128 ≤ (625467929768453/625000000000000 : ℝ)^549 := by
      have hnat : (25080378100358931463 : ℕ)^128*625000000000000^549 ≤ 625467929768453^549*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25080378100358931463 25000000000000000000 625467929768453 625000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625467929768453/625000000000000 : ℝ)) (X := (25080378100358931463/25000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25160753170645978643/25000000000000000000 : ℝ) ≤ (1001497347000457/1000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (25160753170645978643/25000000000000000000 : ℝ)^128 ≤ (1001497347000457/1000000000000000 : ℝ)^549 := by
      have hnat : (25160753170645978643 : ℕ)^128*1000000000000000^549 ≤ 1001497347000457^549*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25160753170645978643 25000000000000000000 1001497347000457 1000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001497347000457/1000000000000000 : ℝ)) (X := (25160753170645978643/25000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3030071884283/50000000000000000000 : ℝ) ≤ ((928880471109612891/929000000000000000 : ℝ)+2*(287945911897/92900000000000 : ℝ)*(519/25000 : ℝ))^(549/128 : ℝ) := by
    rw [show (928880471109612891/929000000000000000 : ℝ)+2*(287945911897/92900000000000 : ℝ)*(519/25000 : ℝ)=(5000000141292963/5000000000000000 : ℝ) by norm_num, show 1+2*(3030071884283/50000000000000000000 : ℝ)=(25000003030071884283/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(160753170645978643/50000000000000000000 : ℝ)+(3030071884283/50000000000000000000 : ℝ) ≤ ((928880471109612891/929000000000000000 : ℝ)+(287945911897/92900000000000 : ℝ)*((2623/10000 : ℝ)+(519/25000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (928880471109612891/929000000000000000 : ℝ)+(287945911897/92900000000000 : ℝ)*((2623/10000 : ℝ)+(519/25000 : ℝ))=(625467929768453/625000000000000 : ℝ) by norm_num, show 1+(160753170645978643/50000000000000000000 : ℝ)+(3030071884283/50000000000000000000 : ℝ)=(25080378100358931463/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(160753170645978643/50000000000000000000 : ℝ) ≤ ((928880471109612891/929000000000000000 : ℝ)+2*(287945911897/92900000000000 : ℝ)*(2623/10000 : ℝ))^(549/128 : ℝ) := by
    rw [show (928880471109612891/929000000000000000 : ℝ)+2*(287945911897/92900000000000 : ℝ)*(2623/10000 : ℝ)=(1001497347000457/1000000000000000 : ℝ) by norm_num, show 1+2*(160753170645978643/50000000000000000000 : ℝ)=(25160753170645978643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (928880471109612891/929000000000000000 : ℝ)*(X 1 0+X 2 0)+(287945911897/92900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (519/25000 : ℝ)) (hi := (2623/10000 : ℝ)) (c := (928880471109612891/929000000000000000 : ℝ)) (alpha := (287945911897/92900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (928880471109612891/929000000000000000 : ℝ)*(X 0 1+X 2 1)+(287945911897/92900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (519/25000 : ℝ)) (hi := (2623/10000 : ℝ)) (c := (928880471109612891/929000000000000000 : ℝ)) (alpha := (287945911897/92900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (928880471109612891/929000000000000000 : ℝ)*(X 0 2+X 1 2)+(287945911897/92900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (519/25000 : ℝ)) (hi := (2623/10000 : ℝ)) (c := (928880471109612891/929000000000000000 : ℝ)) (alpha := (287945911897/92900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1928343967/10000000000 : ℝ)*X 0 0+(5603616903/10000000000 : ℝ)*X 0 1+(5076927777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5396406121/10000000000 : ℝ)*X 1 0+(-1103672053/5000000000 : ℝ)*X 1 1+(2538464671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53964073/100000000 : ℝ)*X 2 0+(126923201/250000000 : ℝ)*X 2 1+(-551836059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4275913249/10000000000 : ℝ)*X 0 0+(233706169/625000000 : ℝ)*X 0 1+(4880370739/10000000000 : ℝ)*X 0 2+(4275913249/10000000000 : ℝ)*X 1 0+(233706169/625000000 : ℝ)*X 1 1+(4880370739/10000000000 : ℝ)*X 1 2+(4275913249/10000000000 : ℝ)*X 2 0+(233706169/625000000 : ℝ)*X 2 1+(4880370739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-964368199/5000000000 : ℝ)*X 0 0+(5083084421/10000000000 : ℝ)*X 0 1+(5597356293/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258756499/10000000000 : ℝ)*X 1 0+(-67476659/400000000 : ℝ)*X 1 1+(5597356311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629378221/5000000000 : ℝ)*X 2 0+(349834767/625000000 : ℝ)*X 2 1+(-1686916611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4276764233/10000000000 : ℝ)*X 0 0+(2433516781/5000000000 : ℝ)*X 0 1+(3752860511/10000000000 : ℝ)*X 0 2+(4276764233/10000000000 : ℝ)*X 1 0+(2433516781/5000000000 : ℝ)*X 1 1+(3752860511/10000000000 : ℝ)*X 1 2+(4276764233/10000000000 : ℝ)*X 2 0+(2433516781/5000000000 : ℝ)*X 2 1+(3752860511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15266221457283869349249693/5806250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181615059/50000000000000 : ℝ)*(base19) + (166137953/25000000000000 : ℝ)*(base23) + (63988467/100000000000000 : ℝ)*(upper3) + (61247459/100000000000000 : ℝ)*(upper4) + (1056527/12500000000000 : ℝ)*(upper5) + (173440108618259/12500000000000 : ℝ)*(major0) + (173440108618259/12500000000000 : ℝ)*(major1) + (173440108618259/12500000000000 : ℝ)*(major2) + (474665029313527/25000000000000 : ℝ)*(sp0) + (949333835037171/50000000000000 : ℝ)*(sp1) + (237333421094081/12500000000000 : ℝ)*(sp2) + (438185389521639/50000000000000 : ℝ)*(sp3) + (494753147/6250000000000 : ℝ)*(sp4) + (2837901939/100000000000000 : ℝ)*(sp7) + (876373616945217/100000000000000 : ℝ)*(f.failure) + (94933401665223/5000000000000 : ℝ)*(f.sum) + (2000599052081/4645000000000000000000000000 : ℝ)*base66 + (57799107487181769/11612500000000000000000000000000 : ℝ)*base67 + (33811372893230731/11612500000000000000000000000000 : ℝ)*base70 + (105932417804619269/11612500000000000000000000000000 : ℝ)*base71 + (5221212654113/2322500000000000000000000000 : ℝ)*base74 + (43989960371330731/11612500000000000000000000000000 : ℝ)*base76 + (61018948758094269/11612500000000000000000000000000 : ℝ)*base77 + (94753610318231769/11612500000000000000000000000000 : ℝ)*base79 + (29436184094651/4645000000000000000000000000 : ℝ)*base82 + (5897939/10000000000000000000000 : ℝ)*base89 + (5897939/10000000000000000000000 : ℝ)*base91 + (5897939/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46500225670379869700787/4645000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87691967/100000000000000 : ℝ)*(base1) + (2070212983/100000000000000 : ℝ)*(base19) + (2040303849/100000000000000 : ℝ)*(base23) + (119574371/50000000000000 : ℝ)*(upper3) + (215955317/100000000000000 : ℝ)*(upper5) + (1421011727067479/100000000000000 : ℝ)*(major0) + (1421011727067479/100000000000000 : ℝ)*(major1) + (1421011727067479/100000000000000 : ℝ)*(major2) + (12042190037/100000000000000 : ℝ)*(sp1) + (2857579/24414062500 : ℝ)*(sp2) + (1944496392613889/100000000000000 : ℝ)*(sp4) + (972241096259451/50000000000000 : ℝ)*(sp5) + (1944482559974489/100000000000000 : ℝ)*(sp6) + (897526727827301/100000000000000 : ℝ)*(sp7) + (224381703879817/25000000000000 : ℝ)*(f.failure) + (972248152460961/50000000000000 : ℝ)*(f.sum) + (942215132983/1161250000000000000000000000 : ℝ)*base66 + (369498010162001789/92900000000000000000000000000000 : ℝ)*base67 + (84593925053298211/92900000000000000000000000000000 : ℝ)*base70 + (189535754971298211/92900000000000000000000000000000 : ℝ)*base72 + (20617206756887/4645000000000000000000000000 : ℝ)*base74 + (512892174209601789/92900000000000000000000000000000 : ℝ)*base75 + (653600124853998211/92900000000000000000000000000000 : ℝ)*base78 + (988609891664901789/92900000000000000000000000000000 : ℝ)*base79 + (19099213408497/4645000000000000000000000000 : ℝ)*base82 + (12563861/2500000000000000000000 : ℝ)*base90 + (12563861/2500000000000000000000 : ℝ)*base92 + (12563861/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1433_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2623/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1537/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (941/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1433_s2_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961173017/10000000000 : ℝ)*x 0 + (5457281121/10000000000 : ℝ)*x 1 + (2601063837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961173017/10000000000 : ℝ)^4393 ≤ (5976510815829/50000000000000 : ℝ)^3369 := by
    have hnat : (1961173017 : ℕ)^4393*50000000000000^3369 ≤ 5976510815829^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961173017 10000000000 5976510815829 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457281121/10000000000 : ℝ)^4393 ≤ (22698694214483/50000000000000 : ℝ)^3369 := by
    have hnat : (5457281121 : ℕ)^4393*50000000000000^3369 ≤ 22698694214483^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457281121 10000000000 22698694214483 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601063837/5000000000 : ℝ)^4393 ≤ (42649589922763/100000000000000 : ℝ)^3369 := by
    have hnat : (2601063837 : ℕ)^4393*100000000000000^3369 ≤ 42649589922763^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601063837 5000000000 42649589922763 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961173017/10000000000 : ℝ), (5457281121/10000000000 : ℝ), (2601063837/5000000000 : ℝ)] ![(5976510815829/50000000000000 : ℝ), (22698694214483/50000000000000 : ℝ), (42649589922763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961173017/10000000000 : ℝ)|^4393 ≤ (5976510815829/50000000000000 : ℝ)^3369
        have hw : |(-1961173017/10000000000 : ℝ)|=(1961173017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457281121/10000000000 : ℝ)|^4393 ≤ (22698694214483/50000000000000 : ℝ)^3369
        have hw : |(5457281121/10000000000 : ℝ)|=(5457281121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601063837/5000000000 : ℝ)|^4393 ≤ (42649589922763/100000000000000 : ℝ)^3369
        have hw : |(2601063837/5000000000 : ℝ)|=(2601063837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s2_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679944173/5000000000 : ℝ)*x 0 + (-2092425277/10000000000 : ℝ)*x 1 + (5202127553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679944173/5000000000 : ℝ)^4393 ≤ (44343833796269/100000000000000 : ℝ)^3369 := by
    have hnat : (2679944173 : ℕ)^4393*100000000000000^3369 ≤ 44343833796269^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679944173 5000000000 44343833796269 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092425277/10000000000 : ℝ)^4393 ≤ (2601315510959/20000000000000 : ℝ)^3369 := by
    have hnat : (2092425277 : ℕ)^4393*20000000000000^3369 ≤ 2601315510959^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092425277 10000000000 2601315510959 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5202127553/10000000000 : ℝ)^4393 ≤ (1705983545169/4000000000000 : ℝ)^3369 := by
    have hnat : (5202127553 : ℕ)^4393*4000000000000^3369 ≤ 1705983545169^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202127553 10000000000 1705983545169 4000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679944173/5000000000 : ℝ), (-2092425277/10000000000 : ℝ), (5202127553/10000000000 : ℝ)] ![(44343833796269/100000000000000 : ℝ), (2601315510959/20000000000000 : ℝ), (1705983545169/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679944173/5000000000 : ℝ)|^4393 ≤ (44343833796269/100000000000000 : ℝ)^3369
        have hw : |(2679944173/5000000000 : ℝ)|=(2679944173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092425277/10000000000 : ℝ)|^4393 ≤ (2601315510959/20000000000000 : ℝ)^3369
        have hw : |(-2092425277/10000000000 : ℝ)|=(2092425277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5202127553/10000000000 : ℝ)|^4393 ≤ (1705983545169/4000000000000 : ℝ)^3369
        have hw : |(5202127553/10000000000 : ℝ)|=(5202127553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s2_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359887939/10000000000 : ℝ)*x 0 + (650266001/1250000000 : ℝ)*x 1 + (-2092425219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359887939/10000000000 : ℝ)^4393 ≤ (22171914702793/50000000000000 : ℝ)^3369 := by
    have hnat : (5359887939 : ℕ)^4393*50000000000000^3369 ≤ 22171914702793^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359887939 10000000000 22171914702793 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650266001/1250000000 : ℝ)^4393 ≤ (21324796746679/50000000000000 : ℝ)^3369 := by
    have hnat : (650266001 : ℕ)^4393*50000000000000^3369 ≤ 21324796746679^3369*1250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650266001 1250000000 21324796746679 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092425219/10000000000 : ℝ)^4393 ≤ (13006577084683/100000000000000 : ℝ)^3369 := by
    have hnat : (2092425219 : ℕ)^4393*100000000000000^3369 ≤ 13006577084683^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092425219 10000000000 13006577084683 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359887939/10000000000 : ℝ), (650266001/1250000000 : ℝ), (-2092425219/10000000000 : ℝ)] ![(22171914702793/50000000000000 : ℝ), (21324796746679/50000000000000 : ℝ), (13006577084683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359887939/10000000000 : ℝ)|^4393 ≤ (22171914702793/50000000000000 : ℝ)^3369
        have hw : |(5359887939/10000000000 : ℝ)|=(5359887939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650266001/1250000000 : ℝ)|^4393 ≤ (21324796746679/50000000000000 : ℝ)^3369
        have hw : |(650266001/1250000000 : ℝ)|=(650266001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092425219/10000000000 : ℝ)|^4393 ≤ (13006577084683/100000000000000 : ℝ)^3369
        have hw : |(-2092425219/10000000000 : ℝ)|=(2092425219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s2_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149549769/5000000000 : ℝ)*x 0 + (4030665769/10000000000 : ℝ)*x 1 + (2291728699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149549769/5000000000 : ℝ)^4393 ≤ (6652324242519/20000000000000 : ℝ)^3369 := by
    have hnat : (2149549769 : ℕ)^4393*20000000000000^3369 ≤ 6652324242519^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149549769 5000000000 6652324242519 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030665769/10000000000 : ℝ)^4393 ≤ (6115922050089/20000000000000 : ℝ)^3369 := by
    have hnat : (4030665769 : ℕ)^4393*20000000000000^3369 ≤ 6115922050089^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030665769 10000000000 6115922050089 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291728699/5000000000 : ℝ)^4393 ≤ (18079384265943/50000000000000 : ℝ)^3369 := by
    have hnat : (2291728699 : ℕ)^4393*50000000000000^3369 ≤ 18079384265943^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291728699 5000000000 18079384265943 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149549769/5000000000 : ℝ), (4030665769/10000000000 : ℝ), (2291728699/5000000000 : ℝ)] ![(6652324242519/20000000000000 : ℝ), (6115922050089/20000000000000 : ℝ), (18079384265943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149549769/5000000000 : ℝ)|^4393 ≤ (6652324242519/20000000000000 : ℝ)^3369
        have hw : |(2149549769/5000000000 : ℝ)|=(2149549769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030665769/10000000000 : ℝ)|^4393 ≤ (6115922050089/20000000000000 : ℝ)^3369
        have hw : |(4030665769/10000000000 : ℝ)|=(4030665769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2291728699/5000000000 : ℝ)|^4393 ≤ (18079384265943/50000000000000 : ℝ)^3369
        have hw : |(2291728699/5000000000 : ℝ)|=(2291728699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s2_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-980608901/5000000000 : ℝ)*x 0 + (520358159/1000000000 : ℝ)*x 1 + (5455815279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980608901/5000000000 : ℝ)^4393 ≤ (478135102187/4000000000000 : ℝ)^3369 := by
    have hnat : (980608901 : ℕ)^4393*4000000000000^3369 ≤ 478135102187^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980608901 5000000000 478135102187 4000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520358159/1000000000 : ℝ)^4393 ≤ (42665133529723/100000000000000 : ℝ)^3369 := by
    have hnat : (520358159 : ℕ)^4393*100000000000000^3369 ≤ 42665133529723^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520358159 1000000000 42665133529723 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455815279/10000000000 : ℝ)^4393 ≤ (1134537222583/2500000000000 : ℝ)^3369 := by
    have hnat : (5455815279 : ℕ)^4393*2500000000000^3369 ≤ 1134537222583^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455815279 10000000000 1134537222583 2500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-980608901/5000000000 : ℝ), (520358159/1000000000 : ℝ), (5455815279/10000000000 : ℝ)] ![(478135102187/4000000000000 : ℝ), (42665133529723/100000000000000 : ℝ), (1134537222583/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-980608901/5000000000 : ℝ)|^4393 ≤ (478135102187/4000000000000 : ℝ)^3369
        have hw : |(-980608901/5000000000 : ℝ)|=(980608901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520358159/1000000000 : ℝ)|^4393 ≤ (42665133529723/100000000000000 : ℝ)^3369
        have hw : |(520358159/1000000000 : ℝ)|=(520358159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455815279/10000000000 : ℝ)|^4393 ≤ (1134537222583/2500000000000 : ℝ)^3369
        have hw : |(5455815279/10000000000 : ℝ)|=(5455815279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s2_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646757459/5000000000 : ℝ)*x 0 + (-183873717/1000000000 : ℝ)*x 1 + (5455815817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646757459/5000000000 : ℝ)^4393 ≤ (1745166161571/4000000000000 : ℝ)^3369 := by
    have hnat : (2646757459 : ℕ)^4393*4000000000000^3369 ≤ 1745166161571^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646757459 5000000000 1745166161571 4000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183873717/1000000000 : ℝ)^4393 ≤ (2747337800087/25000000000000 : ℝ)^3369 := by
    have hnat : (183873717 : ℕ)^4393*25000000000000^3369 ≤ 2747337800087^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183873717 1000000000 2747337800087 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455815817/10000000000 : ℝ)^4393 ≤ (22690747369299/50000000000000 : ℝ)^3369 := by
    have hnat : (5455815817 : ℕ)^4393*50000000000000^3369 ≤ 22690747369299^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455815817 10000000000 22690747369299 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646757459/5000000000 : ℝ), (-183873717/1000000000 : ℝ), (5455815817/10000000000 : ℝ)] ![(1745166161571/4000000000000 : ℝ), (2747337800087/25000000000000 : ℝ), (22690747369299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646757459/5000000000 : ℝ)|^4393 ≤ (1745166161571/4000000000000 : ℝ)^3369
        have hw : |(2646757459/5000000000 : ℝ)|=(2646757459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-183873717/1000000000 : ℝ)|^4393 ≤ (2747337800087/25000000000000 : ℝ)^3369
        have hw : |(-183873717/1000000000 : ℝ)|=(183873717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455815817/10000000000 : ℝ)|^4393 ≤ (22690747369299/50000000000000 : ℝ)^3369
        have hw : |(5455815817/10000000000 : ℝ)|=(5455815817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s2_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264675737/500000000 : ℝ)*x 0 + (272790789/500000000 : ℝ)*x 1 + (-459684367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264675737/500000000 : ℝ)^4393 ≤ (10907288031571/25000000000000 : ℝ)^3369 := by
    have hnat : (264675737 : ℕ)^4393*25000000000000^3369 ≤ 10907288031571^3369*500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264675737 500000000 10907288031571 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272790789/500000000 : ℝ)^4393 ≤ (45381494337287/100000000000000 : ℝ)^3369 := by
    have hnat : (272790789 : ℕ)^4393*100000000000000^3369 ≤ 45381494337287^3369*500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272790789 500000000 45381494337287 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459684367/2500000000 : ℝ)^4393 ≤ (686834595169/6250000000000 : ℝ)^3369 := by
    have hnat : (459684367 : ℕ)^4393*6250000000000^3369 ≤ 686834595169^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459684367 2500000000 686834595169 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264675737/500000000 : ℝ), (272790789/500000000 : ℝ), (-459684367/2500000000 : ℝ)] ![(10907288031571/25000000000000 : ℝ), (45381494337287/100000000000000 : ℝ), (686834595169/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264675737/500000000 : ℝ)|^4393 ≤ (10907288031571/25000000000000 : ℝ)^3369
        have hw : |(264675737/500000000 : ℝ)|=(264675737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272790789/500000000 : ℝ)|^4393 ≤ (45381494337287/100000000000000 : ℝ)^3369
        have hw : |(272790789/500000000 : ℝ)|=(272790789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-459684367/2500000000 : ℝ)|^4393 ≤ (686834595169/6250000000000 : ℝ)^3369
        have hw : |(-459684367/2500000000 : ℝ)|=(459684367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s2_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299196473/10000000000 : ℝ)*x 0 + (2290153963/5000000000 : ℝ)*x 1 + (403384113/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299196473/10000000000 : ℝ)^4393 ≤ (33262599143583/100000000000000 : ℝ)^3369 := by
    have hnat : (4299196473 : ℕ)^4393*100000000000000^3369 ≤ 33262599143583^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299196473 10000000000 33262599143583 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2290153963/5000000000 : ℝ)^4393 ≤ (9031593475651/25000000000000 : ℝ)^3369 := by
    have hnat : (2290153963 : ℕ)^4393*25000000000000^3369 ≤ 9031593475651^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290153963 5000000000 9031593475651 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403384113/1000000000 : ℝ)^4393 ≤ (30611026941469/100000000000000 : ℝ)^3369 := by
    have hnat : (403384113 : ℕ)^4393*100000000000000^3369 ≤ 30611026941469^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403384113 1000000000 30611026941469 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299196473/10000000000 : ℝ), (2290153963/5000000000 : ℝ), (403384113/1000000000 : ℝ)] ![(33262599143583/100000000000000 : ℝ), (9031593475651/25000000000000 : ℝ), (30611026941469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299196473/10000000000 : ℝ)|^4393 ≤ (33262599143583/100000000000000 : ℝ)^3369
        have hw : |(4299196473/10000000000 : ℝ)|=(4299196473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2290153963/5000000000 : ℝ)|^4393 ≤ (9031593475651/25000000000000 : ℝ)^3369
        have hw : |(2290153963/5000000000 : ℝ)|=(2290153963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403384113/1000000000 : ℝ)|^4393 ≤ (30611026941469/100000000000000 : ℝ)^3369
        have hw : |(403384113/1000000000 : ℝ)|=(403384113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (941/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1537/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15787/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (941/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1537/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (941/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1537/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (941/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1537/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (941/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1537/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (941/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1537/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (941/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1537/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1537/20000 : ℝ) ^ (549/128 : ℝ) ≤ (830666934660301/50000000000000000000 : ℝ) := by
    have hpowers : (1537/20000 : ℝ)^549 ≤ (830666934660301/50000000000000000000 : ℝ)^128 := by
      have hnat : (1537 : ℕ)^549*50000000000000000000^128 ≤ 830666934660301^128*20000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1537 20000 830666934660301 50000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1537/20000 : ℝ)) (X := (830666934660301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (941/5000 : ℝ) ^ (549/128 : ℝ) ≤ (38705101826131109/50000000000000000000 : ℝ) := by
    have hpowers : (941/5000 : ℝ)^549 ≤ (38705101826131109/50000000000000000000 : ℝ)^128 := by
      have hnat : (941 : ℕ)^549*50000000000000000000^128 ≤ 38705101826131109^128*5000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        941 5000 38705101826131109 50000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (941/5000 : ℝ)) (X := (38705101826131109/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000830666934660301/25000000000000000000 : ℝ) ≤ (10000077467404799/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (25000830666934660301/25000000000000000000 : ℝ)^128 ≤ (10000077467404799/10000000000000000 : ℝ)^549 := by
      have hnat : (25000830666934660301 : ℕ)^128*10000000000000000^549 ≤ 10000077467404799^549*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000830666934660301 25000000000000000000 10000077467404799 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000077467404799/10000000000000000 : ℝ)) (X := (25000830666934660301/25000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (5003953576876079141/5000000000000000000 : ℝ) ≤ (10001843003588881/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (5003953576876079141/5000000000000000000 : ℝ)^128 ≤ (10001843003588881/10000000000000000 : ℝ)^549 := by
      have hnat : (5003953576876079141 : ℕ)^128*10000000000000000^549 ≤ 10001843003588881^549*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003953576876079141 5000000000000000000 10001843003588881 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001843003588881/10000000000000000 : ℝ)) (X := (5003953576876079141/5000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25038705101826131109/25000000000000000000 : ℝ) ≤ (10003608539772963/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (25038705101826131109/25000000000000000000 : ℝ)^128 ≤ (10003608539772963/10000000000000000 : ℝ)^549 := by
      have hnat : (25038705101826131109 : ℕ)^128*10000000000000000^549 ≤ 10003608539772963^549*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038705101826131109 25000000000000000000 10003608539772963 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003608539772963/10000000000000000 : ℝ)) (X := (25038705101826131109/25000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(830666934660301/50000000000000000000 : ℝ) ≤ ((4452949052336123861/4454000000000000000 : ℝ)+2*(882768092041/556750000000000 : ℝ)*(1537/20000 : ℝ))^(549/128 : ℝ) := by
    rw [show (4452949052336123861/4454000000000000000 : ℝ)+2*(882768092041/556750000000000 : ℝ)*(1537/20000 : ℝ)=(10000077467404799/10000000000000000 : ℝ) by norm_num, show 1+2*(830666934660301/50000000000000000000 : ℝ)=(25000830666934660301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38705101826131109/50000000000000000000 : ℝ)+(830666934660301/50000000000000000000 : ℝ) ≤ ((4452949052336123861/4454000000000000000 : ℝ)+(882768092041/556750000000000 : ℝ)*((941/5000 : ℝ)+(1537/20000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (4452949052336123861/4454000000000000000 : ℝ)+(882768092041/556750000000000 : ℝ)*((941/5000 : ℝ)+(1537/20000 : ℝ))=(10001843003588881/10000000000000000 : ℝ) by norm_num, show 1+(38705101826131109/50000000000000000000 : ℝ)+(830666934660301/50000000000000000000 : ℝ)=(5003953576876079141/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38705101826131109/50000000000000000000 : ℝ) ≤ ((4452949052336123861/4454000000000000000 : ℝ)+2*(882768092041/556750000000000 : ℝ)*(941/5000 : ℝ))^(549/128 : ℝ) := by
    rw [show (4452949052336123861/4454000000000000000 : ℝ)+2*(882768092041/556750000000000 : ℝ)*(941/5000 : ℝ)=(10003608539772963/10000000000000000 : ℝ) by norm_num, show 1+2*(38705101826131109/50000000000000000000 : ℝ)=(25038705101826131109/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4452949052336123861/4454000000000000000 : ℝ)*(X 1 0+X 2 0)+(882768092041/556750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (1537/20000 : ℝ)) (hi := (941/5000 : ℝ)) (c := (4452949052336123861/4454000000000000000 : ℝ)) (alpha := (882768092041/556750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4452949052336123861/4454000000000000000 : ℝ)*(X 0 1+X 2 1)+(882768092041/556750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (1537/20000 : ℝ)) (hi := (941/5000 : ℝ)) (c := (4452949052336123861/4454000000000000000 : ℝ)) (alpha := (882768092041/556750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4452949052336123861/4454000000000000000 : ℝ)*(X 0 2+X 1 2)+(882768092041/556750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (1537/20000 : ℝ)) (hi := (941/5000 : ℝ)) (c := (4452949052336123861/4454000000000000000 : ℝ)) (alpha := (882768092041/556750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1961173017/10000000000 : ℝ)*X 0 0+(5457281121/10000000000 : ℝ)*X 0 1+(2601063837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679944173/5000000000 : ℝ)*X 1 0+(-2092425277/10000000000 : ℝ)*X 1 1+(5202127553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5359887939/10000000000 : ℝ)*X 2 0+(650266001/1250000000 : ℝ)*X 2 1+(-2092425219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149549769/5000000000 : ℝ)*X 0 0+(4030665769/10000000000 : ℝ)*X 0 1+(2291728699/5000000000 : ℝ)*X 0 2+(2149549769/5000000000 : ℝ)*X 1 0+(4030665769/10000000000 : ℝ)*X 1 1+(2291728699/5000000000 : ℝ)*X 1 2+(2149549769/5000000000 : ℝ)*X 2 0+(4030665769/10000000000 : ℝ)*X 2 1+(2291728699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-980608901/5000000000 : ℝ)*X 0 0+(520358159/1000000000 : ℝ)*X 0 1+(5455815279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646757459/5000000000 : ℝ)*X 1 0+(-183873717/1000000000 : ℝ)*X 1 1+(5455815817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264675737/500000000 : ℝ)*X 2 0+(272790789/500000000 : ℝ)*X 2 1+(-459684367/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299196473/10000000000 : ℝ)*X 0 0+(2290153963/5000000000 : ℝ)*X 0 1+(403384113/1000000000 : ℝ)*X 0 2+(4299196473/10000000000 : ℝ)*X 1 0+(2290153963/5000000000 : ℝ)*X 1 1+(403384113/1000000000 : ℝ)*X 1 2+(4299196473/10000000000 : ℝ)*X 2 0+(2290153963/5000000000 : ℝ)*X 2 1+(403384113/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298512688490482485556060977/55675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153621519/25000000000000 : ℝ)*(base19) + (98942081/100000000000000 : ℝ)*(base23) + (29203401/25000000000000 : ℝ)*(lower2) + (37410809/20000000000000 : ℝ)*(upper3) + (4100999/50000000000000 : ℝ)*(upper5) + (1432056163254319/50000000000000 : ℝ)*(major0) + (1432056163254319/50000000000000 : ℝ)*(major1) + (1432056163254319/50000000000000 : ℝ)*(major2) + (3919216886974607/100000000000000 : ℝ)*(sp0) + (489902331405023/12500000000000 : ℝ)*(sp1) + (1959609583392089/50000000000000 : ℝ)*(sp2) + (180900168509091/10000000000000 : ℝ)*(sp3) + (594687913/25000000000000 : ℝ)*(sp4) + (176173837/5000000000000 : ℝ)*(sp7) + (36180104171353/2000000000000 : ℝ)*(f.failure) + (195960963286313/5000000000000 : ℝ)*(f.sum) + (35285172964159/55675000000000000000000000000 : ℝ)*base66 + (657863538136062341/222700000000000000000000000000000 : ℝ)*base68 + (218471818711637659/222700000000000000000000000000000 : ℝ)*base69 + (580709369664962341/222700000000000000000000000000000 : ℝ)*base72 + (38969961449233/27837500000000000000000000000 : ℝ)*base73 + (5943442257768562341/222700000000000000000000000000000 : ℝ)*base76 + (1562757015215562341/222700000000000000000000000000000 : ℝ)*base78 + (2561564669477962341/222700000000000000000000000000000 : ℝ)*base80 + (2396934791667/27837500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1476251/200000000000000000000 : ℝ)*base89 + (1476251/200000000000000000000 : ℝ)*base91 + (1476251/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62893735877406017837866383/13918750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2465437/12500000000000 : ℝ)*(base19) + (6966451/10000000000000 : ℝ)*(base23) + (37127407/25000000000000 : ℝ)*(upper3) + (23849419/25000000000000 : ℝ)*(lower4) + (181078444163399/6250000000000 : ℝ)*(major0) + (181078444163399/6250000000000 : ℝ)*(major1) + (181078444163399/6250000000000 : ℝ)*(major2) + (2906994541/100000000000000 : ℝ)*(sp1) + (3149277883/100000000000000 : ℝ)*(sp2) + (74188177/25000000000000 : ℝ)*(sp3) + (247785719088311/6250000000000 : ℝ)*(sp4) + (1982284289347469/50000000000000 : ℝ)*(sp5) + (1982284143235291/50000000000000 : ℝ)*(sp6) + (914969130220973/50000000000000 : ℝ)*(sp7) + (914969278597327/50000000000000 : ℝ)*(f.failure) + (247785719088311/6250000000000 : ℝ)*(f.sum) + (114072771238131/27837500000000000000000000000 : ℝ)*base66 + (39933250878435539/27837500000000000000000000000000 : ℝ)*base67 + (1021860315185539/27837500000000000000000000000000 : ℝ)*base69 + (130100463535164461/27837500000000000000000000000000 : ℝ)*base72 + (94801218407937/55675000000000000000000000000 : ℝ)*base74 + (433915523405123039/27837500000000000000000000000000 : ℝ)*base75 + (34866359124776961/27837500000000000000000000000000 : ℝ)*base78 + (188866125593835539/27837500000000000000000000000000 : ℝ)*base79 + (24673928201937/55675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17238691/5000000000000000000000 : ℝ)*base90 + (17238691/5000000000000000000000 : ℝ)*base92 + (17238691/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1433_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (941/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1537/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15787/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1433_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15787/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1433_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1433_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1433_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15787/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1433_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
