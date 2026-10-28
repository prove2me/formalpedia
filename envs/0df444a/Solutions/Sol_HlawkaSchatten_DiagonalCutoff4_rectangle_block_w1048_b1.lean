-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1048_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:53:07.876367+00:00
-- url     : https://prove2.me/submissions/f717e96b-7950-468a-a5a6-1446dc9cffd8

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
theorem support_rectangle_w1048_s3_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1103835313/5000000000 : ℝ)*x 0 + (169989943/312500000 : ℝ)*x 1 + (1305592941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103835313/5000000000 : ℝ)^8241 ≤ (107168213571/800000000000 : ℝ)^6193 := by
    have hnat : (1103835313 : ℕ)^8241*800000000000^6193 ≤ 107168213571^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103835313 5000000000 107168213571 800000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169989943/312500000 : ℝ)^8241 ≤ (44476267921107/100000000000000 : ℝ)^6193 := by
    have hnat : (169989943 : ℕ)^8241*100000000000000^6193 ≤ 44476267921107^6193*312500000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169989943 312500000 44476267921107 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305592941/2500000000 : ℝ)^8241 ≤ (842554107483/2000000000000 : ℝ)^6193 := by
    have hnat : (1305592941 : ℕ)^8241*2000000000000^6193 ≤ 842554107483^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305592941 2500000000 842554107483 2000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1103835313/5000000000 : ℝ), (169989943/312500000 : ℝ), (1305592941/2500000000 : ℝ)] ![(107168213571/800000000000 : ℝ), (44476267921107/100000000000000 : ℝ), (842554107483/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1103835313/5000000000 : ℝ)|^8241 ≤ (107168213571/800000000000 : ℝ)^6193
        have hw : |(-1103835313/5000000000 : ℝ)|=(1103835313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169989943/312500000 : ℝ)|^8241 ≤ (44476267921107/100000000000000 : ℝ)^6193
        have hw : |(169989943/312500000 : ℝ)|=(169989943/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305592941/2500000000 : ℝ)|^8241 ≤ (842554107483/2000000000000 : ℝ)^6193
        have hw : |(1305592941/2500000000 : ℝ)|=(1305592941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s3_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356161787/10000000000 : ℝ)*x 0 + (-2318999963/10000000000 : ℝ)*x 1 + (261118599/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356161787/10000000000 : ℝ)^8241 ≤ (43569913717003/100000000000000 : ℝ)^6193 := by
    have hnat : (5356161787 : ℕ)^8241*100000000000000^6193 ≤ 43569913717003^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356161787 10000000000 43569913717003 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2318999963/10000000000 : ℝ)^8241 ≤ (1430237857647/10000000000000 : ℝ)^6193 := by
    have hnat : (2318999963 : ℕ)^8241*10000000000000^6193 ≤ 1430237857647^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318999963 10000000000 1430237857647 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261118599/500000000 : ℝ)^8241 ≤ (21063853846393/50000000000000 : ℝ)^6193 := by
    have hnat : (261118599 : ℕ)^8241*50000000000000^6193 ≤ 21063853846393^6193*500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261118599 500000000 21063853846393 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356161787/10000000000 : ℝ), (-2318999963/10000000000 : ℝ), (261118599/500000000 : ℝ)] ![(43569913717003/100000000000000 : ℝ), (1430237857647/10000000000000 : ℝ), (21063853846393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356161787/10000000000 : ℝ)|^8241 ≤ (43569913717003/100000000000000 : ℝ)^6193
        have hw : |(5356161787/10000000000 : ℝ)|=(5356161787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2318999963/10000000000 : ℝ)|^8241 ≤ (1430237857647/10000000000000 : ℝ)^6193
        have hw : |(-2318999963/10000000000 : ℝ)|=(2318999963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261118599/500000000 : ℝ)|^8241 ≤ (21063853846393/50000000000000 : ℝ)^6193
        have hw : |(261118599/500000000 : ℝ)|=(261118599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s3_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1071232369/2000000000 : ℝ)*x 0 + (5222372231/10000000000 : ℝ)*x 1 + (-1159499779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071232369/2000000000 : ℝ)^8241 ≤ (4356991434483/10000000000000 : ℝ)^6193 := by
    have hnat : (1071232369 : ℕ)^8241*10000000000000^6193 ≤ 4356991434483^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071232369 2000000000 4356991434483 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5222372231/10000000000 : ℝ)^8241 ≤ (42127710387127/100000000000000 : ℝ)^6193 := by
    have hnat : (5222372231 : ℕ)^8241*100000000000000^6193 ≤ 42127710387127^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222372231 10000000000 42127710387127 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159499779/5000000000 : ℝ)^8241 ≤ (14302375252621/100000000000000 : ℝ)^6193 := by
    have hnat : (1159499779 : ℕ)^8241*100000000000000^6193 ≤ 14302375252621^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159499779 5000000000 14302375252621 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071232369/2000000000 : ℝ), (5222372231/10000000000 : ℝ), (-1159499779/5000000000 : ℝ)] ![(4356991434483/10000000000000 : ℝ), (42127710387127/100000000000000 : ℝ), (14302375252621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071232369/2000000000 : ℝ)|^8241 ≤ (4356991434483/10000000000000 : ℝ)^6193
        have hw : |(1071232369/2000000000 : ℝ)|=(1071232369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5222372231/10000000000 : ℝ)|^8241 ≤ (42127710387127/100000000000000 : ℝ)^6193
        have hw : |(5222372231/10000000000 : ℝ)|=(5222372231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1159499779/5000000000 : ℝ)|^8241 ≤ (14302375252621/100000000000000 : ℝ)^6193
        have hw : |(-1159499779/5000000000 : ℝ)|=(1159499779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s3_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375137507/10000000000 : ℝ)*x 0 + (1042044983/2500000000 : ℝ)*x 1 + (2296273679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375137507/10000000000 : ℝ)^8241 ≤ (33286575664019/100000000000000 : ℝ)^6193 := by
    have hnat : (4375137507 : ℕ)^8241*100000000000000^6193 ≤ 33286575664019^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375137507 10000000000 33286575664019 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042044983/2500000000 : ℝ)^8241 ≤ (31207881801191/100000000000000 : ℝ)^6193 := by
    have hnat : (1042044983 : ℕ)^8241*100000000000000^6193 ≤ 31207881801191^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042044983 2500000000 31207881801191 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296273679/5000000000 : ℝ)^8241 ≤ (35505542518003/100000000000000 : ℝ)^6193 := by
    have hnat : (2296273679 : ℕ)^8241*100000000000000^6193 ≤ 35505542518003^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296273679 5000000000 35505542518003 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375137507/10000000000 : ℝ), (1042044983/2500000000 : ℝ), (2296273679/5000000000 : ℝ)] ![(33286575664019/100000000000000 : ℝ), (31207881801191/100000000000000 : ℝ), (35505542518003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375137507/10000000000 : ℝ)|^8241 ≤ (33286575664019/100000000000000 : ℝ)^6193
        have hw : |(4375137507/10000000000 : ℝ)|=(4375137507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042044983/2500000000 : ℝ)|^8241 ≤ (31207881801191/100000000000000 : ℝ)^6193
        have hw : |(1042044983/2500000000 : ℝ)|=(1042044983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2296273679/5000000000 : ℝ)|^8241 ≤ (35505542518003/100000000000000 : ℝ)^6193
        have hw : |(2296273679/5000000000 : ℝ)|=(2296273679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s3_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-551923603/2500000000 : ℝ)*x 0 + (2611637501/5000000000 : ℝ)*x 1 + (543876933/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551923603/2500000000 : ℝ)^8241 ≤ (267924375179/2000000000000 : ℝ)^6193 := by
    have hnat : (551923603 : ℕ)^8241*2000000000000^6193 ≤ 267924375179^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551923603 2500000000 267924375179 2000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611637501/5000000000 : ℝ)^8241 ≤ (42137401393503/100000000000000 : ℝ)^6193 := by
    have hnat : (2611637501 : ℕ)^8241*100000000000000^6193 ≤ 42137401393503^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611637501 5000000000 42137401393503 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543876933/1000000000 : ℝ)^8241 ≤ (44466379834377/100000000000000 : ℝ)^6193 := by
    have hnat : (543876933 : ℕ)^8241*100000000000000^6193 ≤ 44466379834377^6193*1000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543876933 1000000000 44466379834377 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551923603/2500000000 : ℝ), (2611637501/5000000000 : ℝ), (543876933/1000000000 : ℝ)] ![(267924375179/2000000000000 : ℝ), (42137401393503/100000000000000 : ℝ), (44466379834377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551923603/2500000000 : ℝ)|^8241 ≤ (267924375179/2000000000000 : ℝ)^6193
        have hw : |(-551923603/2500000000 : ℝ)|=(551923603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611637501/5000000000 : ℝ)|^8241 ≤ (42137401393503/100000000000000 : ℝ)^6193
        have hw : |(2611637501/5000000000 : ℝ)|=(2611637501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543876933/1000000000 : ℝ)|^8241 ≤ (44466379834377/100000000000000 : ℝ)^6193
        have hw : |(543876933/1000000000 : ℝ)|=(543876933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s3_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301500371/10000000000 : ℝ)*x 0 + (-84104083/400000000 : ℝ)*x 1 + (2719384851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301500371/10000000000 : ℝ)^8241 ≤ (42979226482151/100000000000000 : ℝ)^6193 := by
    have hnat : (5301500371 : ℕ)^8241*100000000000000^6193 ≤ 42979226482151^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301500371 10000000000 42979226482151 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84104083/400000000 : ℝ)^8241 ≤ (3138597405519/25000000000000 : ℝ)^6193 := by
    have hnat : (84104083 : ℕ)^8241*25000000000000^6193 ≤ 3138597405519^6193*400000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84104083 400000000 3138597405519 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719384851/5000000000 : ℝ)^8241 ≤ (1111659597039/2500000000000 : ℝ)^6193 := by
    have hnat : (2719384851 : ℕ)^8241*2500000000000^6193 ≤ 1111659597039^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719384851 5000000000 1111659597039 2500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301500371/10000000000 : ℝ), (-84104083/400000000 : ℝ), (2719384851/5000000000 : ℝ)] ![(42979226482151/100000000000000 : ℝ), (3138597405519/25000000000000 : ℝ), (1111659597039/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301500371/10000000000 : ℝ)|^8241 ≤ (42979226482151/100000000000000 : ℝ)^6193
        have hw : |(5301500371/10000000000 : ℝ)|=(5301500371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84104083/400000000 : ℝ)|^8241 ≤ (3138597405519/25000000000000 : ℝ)^6193
        have hw : |(-84104083/400000000 : ℝ)|=(84104083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719384851/5000000000 : ℝ)|^8241 ≤ (1111659597039/2500000000000 : ℝ)^6193
        have hw : |(2719384851/5000000000 : ℝ)|=(2719384851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s3_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301500129/10000000000 : ℝ)*x 0 + (5438769607/10000000000 : ℝ)*x 1 + (-1051301267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301500129/10000000000 : ℝ)^8241 ≤ (42979223871469/100000000000000 : ℝ)^6193 := by
    have hnat : (5301500129 : ℕ)^8241*100000000000000^6193 ≤ 42979223871469^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301500129 10000000000 42979223871469 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438769607/10000000000 : ℝ)^8241 ≤ (8893276569601/20000000000000 : ℝ)^6193 := by
    have hnat : (5438769607 : ℕ)^8241*20000000000000^6193 ≤ 8893276569601^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438769607 10000000000 8893276569601 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051301267/5000000000 : ℝ)^8241 ≤ (3138598317257/25000000000000 : ℝ)^6193 := by
    have hnat : (1051301267 : ℕ)^8241*25000000000000^6193 ≤ 3138598317257^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051301267 5000000000 3138598317257 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301500129/10000000000 : ℝ), (5438769607/10000000000 : ℝ), (-1051301267/5000000000 : ℝ)] ![(42979223871469/100000000000000 : ℝ), (8893276569601/20000000000000 : ℝ), (3138598317257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301500129/10000000000 : ℝ)|^8241 ≤ (42979223871469/100000000000000 : ℝ)^6193
        have hw : |(5301500129/10000000000 : ℝ)|=(5301500129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438769607/10000000000 : ℝ)|^8241 ≤ (8893276569601/20000000000000 : ℝ)^6193
        have hw : |(5438769607/10000000000 : ℝ)|=(5438769607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051301267/5000000000 : ℝ)|^8241 ≤ (3138598317257/25000000000000 : ℝ)^6193
        have hw : |(-1051301267/5000000000 : ℝ)|=(1051301267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s3_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187591553/5000000000 : ℝ)*x 0 + (4590784827/10000000000 : ℝ)*x 1 + (833990663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187591553/5000000000 : ℝ)^8241 ≤ (33287037313459/100000000000000 : ℝ)^6193 := by
    have hnat : (2187591553 : ℕ)^8241*100000000000000^6193 ≤ 33287037313459^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187591553 5000000000 33287037313459 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4590784827/10000000000 : ℝ)^8241 ≤ (8871852787783/25000000000000 : ℝ)^6193 := by
    have hnat : (4590784827 : ℕ)^8241*25000000000000^6193 ≤ 8871852787783^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590784827 10000000000 8871852787783 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833990663/2000000000 : ℝ)^8241 ≤ (6245110304967/20000000000000 : ℝ)^6193 := by
    have hnat : (833990663 : ℕ)^8241*20000000000000^6193 ≤ 6245110304967^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833990663 2000000000 6245110304967 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187591553/5000000000 : ℝ), (4590784827/10000000000 : ℝ), (833990663/2000000000 : ℝ)] ![(33287037313459/100000000000000 : ℝ), (8871852787783/25000000000000 : ℝ), (6245110304967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187591553/5000000000 : ℝ)|^8241 ≤ (33287037313459/100000000000000 : ℝ)^6193
        have hw : |(2187591553/5000000000 : ℝ)|=(2187591553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4590784827/10000000000 : ℝ)|^8241 ≤ (8871852787783/25000000000000 : ℝ)^6193
        have hw : |(4590784827/10000000000 : ℝ)|=(4590784827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833990663/2000000000 : ℝ)|^8241 ≤ (6245110304967/20000000000000 : ℝ)^6193
        have hw : |(833990663/2000000000 : ℝ)|=(833990663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2067/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14933/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4311/50000 : ℝ) ^ (515/128 : ℝ) ≤ (5217775473483869/100000000000000000000 : ℝ) := by
    have hpowers : (4311/50000 : ℝ)^515 ≤ (5217775473483869/100000000000000000000 : ℝ)^128 := by
      have hnat : (4311 : ℕ)^515*100000000000000000000^128 ≤ 5217775473483869^128*50000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4311 50000 5217775473483869 100000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4311/50000 : ℝ)) (X := (5217775473483869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (16801/100000 : ℝ) ^ (515/128 : ℝ) ≤ (15283200656271767/20000000000000000000 : ℝ) := by
    have hpowers : (16801/100000 : ℝ)^515 ≤ (15283200656271767/20000000000000000000 : ℝ)^128 := by
      have hnat : (16801 : ℕ)^515*20000000000000000000^128 ≤ 15283200656271767^128*100000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16801 100000 15283200656271767 20000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16801/100000 : ℝ)) (X := (15283200656271767/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005217775473483869/50000000000000000000 : ℝ) ≤ (5000129679432093/5000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (50005217775473483869/50000000000000000000 : ℝ)^128 ≤ (5000129679432093/5000000000000000 : ℝ)^515 := by
      have hnat : (50005217775473483869 : ℕ)^128*5000000000000000^515 ≤ 5000129679432093^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005217775473483869 50000000000000000000 5000129679432093 5000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000129679432093/5000000000000000 : ℝ)) (X := (50005217775473483869/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (6255102111172177669/6250000000000000000 : ℝ) ≤ (1250253541753413/1250000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (6255102111172177669/6250000000000000000 : ℝ)^128 ≤ (1250253541753413/1250000000000000 : ℝ)^515 := by
      have hnat : (6255102111172177669 : ℕ)^128*1250000000000000^515 ≤ 1250253541753413^515*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6255102111172177669 6250000000000000000 1250253541753413 1250000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250253541753413/1250000000000000 : ℝ)) (X := (6255102111172177669/6250000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10015283200656271767/10000000000000000000 : ℝ) ≤ (5001898654595211/5000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (10015283200656271767/10000000000000000000 : ℝ)^128 ≤ (5001898654595211/5000000000000000 : ℝ)^515 := by
      have hnat : (10015283200656271767 : ℕ)^128*5000000000000000^515 ≤ 5001898654595211^515*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10015283200656271767 10000000000000000000 5001898654595211 5000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001898654595211/5000000000000000 : ℝ)) (X := (10015283200656271767/10000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5217775473483869/100000000000000000000 : ℝ) ≤ ((40880808544218685251/40895000000000000000 : ℝ)+2*(884487581559/408950000000000 : ℝ)*(4311/50000 : ℝ))^(515/128 : ℝ) := by
    rw [show (40880808544218685251/40895000000000000000 : ℝ)+2*(884487581559/408950000000000 : ℝ)*(4311/50000 : ℝ)=(5000129679432093/5000000000000000 : ℝ) by norm_num, show 1+2*(5217775473483869/100000000000000000000 : ℝ)=(50005217775473483869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15283200656271767/20000000000000000000 : ℝ)+(5217775473483869/100000000000000000000 : ℝ) ≤ ((40880808544218685251/40895000000000000000 : ℝ)+(884487581559/408950000000000 : ℝ)*((16801/100000 : ℝ)+(4311/50000 : ℝ)))^(515/128 : ℝ) := by
    rw [show (40880808544218685251/40895000000000000000 : ℝ)+(884487581559/408950000000000 : ℝ)*((16801/100000 : ℝ)+(4311/50000 : ℝ))=(1250253541753413/1250000000000000 : ℝ) by norm_num, show 1+(15283200656271767/20000000000000000000 : ℝ)+(5217775473483869/100000000000000000000 : ℝ)=(6255102111172177669/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15283200656271767/20000000000000000000 : ℝ) ≤ ((40880808544218685251/40895000000000000000 : ℝ)+2*(884487581559/408950000000000 : ℝ)*(16801/100000 : ℝ))^(515/128 : ℝ) := by
    rw [show (40880808544218685251/40895000000000000000 : ℝ)+2*(884487581559/408950000000000 : ℝ)*(16801/100000 : ℝ)=(5001898654595211/5000000000000000 : ℝ) by norm_num, show 1+2*(15283200656271767/20000000000000000000 : ℝ)=(10015283200656271767/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40880808544218685251/40895000000000000000 : ℝ)*(X 1 0+X 2 0)+(884487581559/408950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (4311/50000 : ℝ)) (hi := (16801/100000 : ℝ)) (c := (40880808544218685251/40895000000000000000 : ℝ)) (alpha := (884487581559/408950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40880808544218685251/40895000000000000000 : ℝ)*(X 0 1+X 2 1)+(884487581559/408950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (4311/50000 : ℝ)) (hi := (16801/100000 : ℝ)) (c := (40880808544218685251/40895000000000000000 : ℝ)) (alpha := (884487581559/408950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40880808544218685251/40895000000000000000 : ℝ)*(X 0 2+X 1 2)+(884487581559/408950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (4311/50000 : ℝ)) (hi := (16801/100000 : ℝ)) (c := (40880808544218685251/40895000000000000000 : ℝ)) (alpha := (884487581559/408950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1103835313/5000000000 : ℝ)*X 0 0+(169989943/312500000 : ℝ)*X 0 1+(1305592941/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356161787/10000000000 : ℝ)*X 1 0+(-2318999963/10000000000 : ℝ)*X 1 1+(261118599/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071232369/2000000000 : ℝ)*X 2 0+(5222372231/10000000000 : ℝ)*X 2 1+(-1159499779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375137507/10000000000 : ℝ)*X 0 0+(1042044983/2500000000 : ℝ)*X 0 1+(2296273679/5000000000 : ℝ)*X 0 2+(4375137507/10000000000 : ℝ)*X 1 0+(1042044983/2500000000 : ℝ)*X 1 1+(2296273679/5000000000 : ℝ)*X 1 2+(4375137507/10000000000 : ℝ)*X 2 0+(1042044983/2500000000 : ℝ)*X 2 1+(2296273679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-551923603/2500000000 : ℝ)*X 0 0+(2611637501/5000000000 : ℝ)*X 0 1+(543876933/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301500371/10000000000 : ℝ)*X 1 0+(-84104083/400000000 : ℝ)*X 1 1+(2719384851/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301500129/10000000000 : ℝ)*X 2 0+(5438769607/10000000000 : ℝ)*X 2 1+(-1051301267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187591553/5000000000 : ℝ)*X 0 0+(4590784827/10000000000 : ℝ)*X 0 1+(833990663/2000000000 : ℝ)*X 0 2+(2187591553/5000000000 : ℝ)*X 1 0+(4590784827/10000000000 : ℝ)*X 1 1+(833990663/2000000000 : ℝ)*X 1 2+(2187591553/5000000000 : ℝ)*X 2 0+(4590784827/10000000000 : ℝ)*X 2 1+(833990663/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1812300049564234624596213423/255593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73908189/4000000000000 : ℝ)*(base19) + (1541513519/100000000000000 : ℝ)*(base23) + (190691819/100000000000000 : ℝ)*(lower2) + (40403551/50000000000000 : ℝ)*(upper3) + (202240901/100000000000000 : ℝ)*(upper5) + (869794000313391/25000000000000 : ℝ)*(major0) + (869794000313391/25000000000000 : ℝ)*(major1) + (869794000313391/25000000000000 : ℝ)*(major2) + (2300915662398877/50000000000000 : ℝ)*(sp0) + (4601871129961783/100000000000000 : ℝ)*(sp1) + (4601871436152989/100000000000000 : ℝ)*(sp2) + (117823183551681/5000000000000 : ℝ)*(sp3) + (8330573751/20000000000000 : ℝ)*(sp4) + (7558727677/50000000000000 : ℝ)*(sp7) + (1178239394244487/50000000000000 : ℝ)*(f.failure) + (1150468244416627/25000000000000 : ℝ)*(f.sum) + (302119617139/1277968750000000000000000000 : ℝ)*base66 + (3142261196772103859/1022375000000000000000000000000000 : ℝ)*base68 + (10201116336479103859/1022375000000000000000000000000000 : ℝ)*base70 + (16691811664130478859/1022375000000000000000000000000000 : ℝ)*base72 + (242431453948297/40895000000000000000000000000 : ℝ)*base73 + (737745988772646141/1022375000000000000000000000000000 : ℝ)*base75 + (6866295624209978859/1022375000000000000000000000000000 : ℝ)*base78 + (2728474591128978859/1022375000000000000000000000000000 : ℝ)*base80 + (7423160826981/1277968750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (11614513/5000000000000000000000 : ℝ)*base90 + (11614513/5000000000000000000000 : ℝ)*base92 + (11614513/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9390927619956354640248170913/1022375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (555163251/25000000000000 : ℝ)*(base19) + (1968309459/100000000000000 : ℝ)*(base23) + (170176207/50000000000000 : ℝ)*(upper3) + (981789/20000000000000 : ℝ)*(lower4) + (79883163/100000000000000 : ℝ)*(upper5) + (1754183596013907/50000000000000 : ℝ)*(major0) + (1754183596013907/50000000000000 : ℝ)*(major1) + (1754183596013907/50000000000000 : ℝ)*(major2) + (7811214953/20000000000000 : ℝ)*(sp1) + (17114063043/50000000000000 : ℝ)*(sp2) + (2320241909989767/50000000000000 : ℝ)*(sp4) + (2320221271625883/50000000000000 : ℝ)*(sp5) + (4640447623543989/100000000000000 : ℝ)*(sp6) + (1188125128947973/50000000000000 : ℝ)*(sp7) + (1188125128947973/50000000000000 : ℝ)*(f.failure) + (2320241909989767/50000000000000 : ℝ)*(f.sum) + (1228496327747/638984375000000000000000000 : ℝ)*base66 + (3571666367394414343/2044750000000000000000000000000000 : ℝ)*base68 + (29628596110194414343/2044750000000000000000000000000000 : ℝ)*base70 + (24784880476682664343/2044750000000000000000000000000000 : ℝ)*base72 + (102809400022737/40895000000000000000000000000 : ℝ)*base73 + (30145889667181414343/2044750000000000000000000000000000 : ℝ)*base76 + (6994845968880164343/2044750000000000000000000000000000 : ℝ)*base78 + (19111870897059164343/2044750000000000000000000000000000 : ℝ)*base80 + (20593891534373/2555937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6586973/5000000000000000000000 : ℝ)*base89 + (6586973/5000000000000000000000 : ℝ)*base91 + (6586973/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1048_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1048_s4_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-442305523/2000000000 : ℝ)*x 0 + (84481841/156250000 : ℝ)*x 1 + (5252693399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442305523/2000000000 : ℝ)^8241 ≤ (13427179300069/100000000000000 : ℝ)^6193 := by
    have hnat : (442305523 : ℕ)^8241*100000000000000^6193 ≤ 13427179300069^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442305523 2000000000 13427179300069 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84481841/156250000 : ℝ)^8241 ≤ (44119317878949/100000000000000 : ℝ)^6193 := by
    have hnat : (84481841 : ℕ)^8241*100000000000000^6193 ≤ 44119317878949^6193*156250000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84481841 156250000 44119317878949 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252693399/10000000000 : ℝ)^8241 ≤ (21226751406517/50000000000000 : ℝ)^6193 := by
    have hnat : (5252693399 : ℕ)^8241*50000000000000^6193 ≤ 21226751406517^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252693399 10000000000 21226751406517 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442305523/2000000000 : ℝ), (84481841/156250000 : ℝ), (5252693399/10000000000 : ℝ)] ![(13427179300069/100000000000000 : ℝ), (44119317878949/100000000000000 : ℝ), (21226751406517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442305523/2000000000 : ℝ)|^8241 ≤ (13427179300069/100000000000000 : ℝ)^6193
        have hw : |(-442305523/2000000000 : ℝ)|=(442305523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84481841/156250000 : ℝ)|^8241 ≤ (44119317878949/100000000000000 : ℝ)^6193
        have hw : |(84481841/156250000 : ℝ)|=(84481841/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252693399/10000000000 : ℝ)|^8241 ≤ (21226751406517/50000000000000 : ℝ)^6193
        have hw : |(5252693399/10000000000 : ℝ)|=(5252693399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s4_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2674021981/5000000000 : ℝ)*x 0 + (-572486927/2500000000 : ℝ)*x 1 + (5252692719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674021981/5000000000 : ℝ)^8241 ≤ (5435257942359/12500000000000 : ℝ)^6193 := by
    have hnat : (2674021981 : ℕ)^8241*12500000000000^6193 ≤ 5435257942359^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674021981 5000000000 5435257942359 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572486927/2500000000 : ℝ)^8241 ≤ (14064440954577/100000000000000 : ℝ)^6193 := by
    have hnat : (572486927 : ℕ)^8241*100000000000000^6193 ≤ 14064440954577^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572486927 2500000000 14064440954577 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252692719/10000000000 : ℝ)^8241 ≤ (10613373874909/25000000000000 : ℝ)^6193 := by
    have hnat : (5252692719 : ℕ)^8241*25000000000000^6193 ≤ 10613373874909^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252692719 10000000000 10613373874909 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674021981/5000000000 : ℝ), (-572486927/2500000000 : ℝ), (5252692719/10000000000 : ℝ)] ![(5435257942359/12500000000000 : ℝ), (14064440954577/100000000000000 : ℝ), (10613373874909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674021981/5000000000 : ℝ)|^8241 ≤ (5435257942359/12500000000000 : ℝ)^6193
        have hw : |(2674021981/5000000000 : ℝ)|=(2674021981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-572486927/2500000000 : ℝ)|^8241 ≤ (14064440954577/100000000000000 : ℝ)^6193
        have hw : |(-572486927/2500000000 : ℝ)|=(572486927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252692719/10000000000 : ℝ)|^8241 ≤ (10613373874909/25000000000000 : ℝ)^6193
        have hw : |(5252692719/10000000000 : ℝ)|=(5252692719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s4_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337011231/2500000000 : ℝ)*x 0 + (5252692013/10000000000 : ℝ)*x 1 + (-2289947363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337011231/2500000000 : ℝ)^8241 ≤ (10870518486729/25000000000000 : ℝ)^6193 := by
    have hnat : (1337011231 : ℕ)^8241*25000000000000^6193 ≤ 10870518486729^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337011231 2500000000 10870518486729 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252692013/10000000000 : ℝ)^8241 ≤ (2653342994163/6250000000000 : ℝ)^6193 := by
    have hnat : (5252692013 : ℕ)^8241*6250000000000^6193 ≤ 2653342994163^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252692013 10000000000 2653342994163 6250000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2289947363/10000000000 : ℝ)^8241 ≤ (14064438134929/100000000000000 : ℝ)^6193 := by
    have hnat : (2289947363 : ℕ)^8241*100000000000000^6193 ≤ 14064438134929^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289947363 10000000000 14064438134929 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337011231/2500000000 : ℝ), (5252692013/10000000000 : ℝ), (-2289947363/10000000000 : ℝ)] ![(10870518486729/25000000000000 : ℝ), (2653342994163/6250000000000 : ℝ), (14064438134929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337011231/2500000000 : ℝ)|^8241 ≤ (10870518486729/25000000000000 : ℝ)^6193
        have hw : |(1337011231/2500000000 : ℝ)|=(1337011231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252692013/10000000000 : ℝ)|^8241 ≤ (2653342994163/6250000000000 : ℝ)^6193
        have hw : |(5252692013/10000000000 : ℝ)|=(5252692013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2289947363/10000000000 : ℝ)|^8241 ≤ (14064438134929/100000000000000 : ℝ)^6193
        have hw : |(-2289947363/10000000000 : ℝ)|=(2289947363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s4_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377429109/10000000000 : ℝ)*x 0 + (845910083/2000000000 : ℝ)*x 1 + (4530575121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377429109/10000000000 : ℝ)^8241 ≤ (33309778071289/100000000000000 : ℝ)^6193 := by
    have hnat : (4377429109 : ℕ)^8241*100000000000000^6193 ≤ 33309778071289^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377429109 10000000000 33309778071289 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845910083/2000000000 : ℝ)^8241 ≤ (3977601104293/12500000000000 : ℝ)^6193 := by
    have hnat : (845910083 : ℕ)^8241*12500000000000^6193 ≤ 3977601104293^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845910083 2000000000 3977601104293 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530575121/10000000000 : ℝ)^8241 ≤ (34869413089631/100000000000000 : ℝ)^6193 := by
    have hnat : (4530575121 : ℕ)^8241*100000000000000^6193 ≤ 34869413089631^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530575121 10000000000 34869413089631 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377429109/10000000000 : ℝ), (845910083/2000000000 : ℝ), (4530575121/10000000000 : ℝ)] ![(33309778071289/100000000000000 : ℝ), (3977601104293/12500000000000 : ℝ), (34869413089631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377429109/10000000000 : ℝ)|^8241 ≤ (33309778071289/100000000000000 : ℝ)^6193
        have hw : |(4377429109/10000000000 : ℝ)|=(4377429109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845910083/2000000000 : ℝ)|^8241 ≤ (3977601104293/12500000000000 : ℝ)^6193
        have hw : |(845910083/2000000000 : ℝ)|=(845910083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530575121/10000000000 : ℝ)|^8241 ≤ (34869413089631/100000000000000 : ℝ)^6193
        have hw : |(4530575121/10000000000 : ℝ)|=(4530575121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s4_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211535829/10000000000 : ℝ)*x 0 + (5253147947/10000000000 : ℝ)*x 1 + (5406381477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211535829/10000000000 : ℝ)^8241 ≤ (13427245663101/100000000000000 : ℝ)^6193 := by
    have hnat : (2211535829 : ℕ)^8241*100000000000000^6193 ≤ 13427245663101^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211535829 10000000000 13427245663101 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253147947/10000000000 : ℝ)^8241 ≤ (8491678309113/20000000000000 : ℝ)^6193 := by
    have hnat : (5253147947 : ℕ)^8241*20000000000000^6193 ≤ 8491678309113^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253147947 10000000000 8491678309113 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406381477/10000000000 : ℝ)^8241 ≤ (44114362767591/100000000000000 : ℝ)^6193 := by
    have hnat : (5406381477 : ℕ)^8241*100000000000000^6193 ≤ 44114362767591^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406381477 10000000000 44114362767591 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211535829/10000000000 : ℝ), (5253147947/10000000000 : ℝ), (5406381477/10000000000 : ℝ)] ![(13427245663101/100000000000000 : ℝ), (8491678309113/20000000000000 : ℝ), (44114362767591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211535829/10000000000 : ℝ)|^8241 ≤ (13427245663101/100000000000000 : ℝ)^6193
        have hw : |(-2211535829/10000000000 : ℝ)|=(2211535829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253147947/10000000000 : ℝ)|^8241 ≤ (8491678309113/20000000000000 : ℝ)^6193
        have hw : |(5253147947/10000000000 : ℝ)|=(5253147947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406381477/10000000000 : ℝ)|^8241 ≤ (44114362767591/100000000000000 : ℝ)^6193
        have hw : |(5406381477/10000000000 : ℝ)|=(5406381477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s4_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654637657/5000000000 : ℝ)*x 0 + (-427251839/2000000000 : ℝ)*x 1 + (5406381439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654637657/5000000000 : ℝ)^8241 ≤ (10765780613657/25000000000000 : ℝ)^6193 := by
    have hnat : (2654637657 : ℕ)^8241*25000000000000^6193 ≤ 10765780613657^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654637657 5000000000 10765780613657 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427251839/2000000000 : ℝ)^8241 ≤ (12822515170577/100000000000000 : ℝ)^6193 := by
    have hnat : (427251839 : ℕ)^8241*100000000000000^6193 ≤ 12822515170577^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427251839 2000000000 12822515170577 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406381439/10000000000 : ℝ)^8241 ≤ (8822872470997/20000000000000 : ℝ)^6193 := by
    have hnat : (5406381439 : ℕ)^8241*20000000000000^6193 ≤ 8822872470997^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406381439 10000000000 8822872470997 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654637657/5000000000 : ℝ), (-427251839/2000000000 : ℝ), (5406381439/10000000000 : ℝ)] ![(10765780613657/25000000000000 : ℝ), (12822515170577/100000000000000 : ℝ), (8822872470997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654637657/5000000000 : ℝ)|^8241 ≤ (10765780613657/25000000000000 : ℝ)^6193
        have hw : |(2654637657/5000000000 : ℝ)|=(2654637657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427251839/2000000000 : ℝ)|^8241 ≤ (12822515170577/100000000000000 : ℝ)^6193
        have hw : |(-427251839/2000000000 : ℝ)|=(427251839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406381439/10000000000 : ℝ)|^8241 ≤ (8822872470997/20000000000000 : ℝ)^6193
        have hw : |(5406381439/10000000000 : ℝ)|=(5406381439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s4_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212371013/400000000 : ℝ)*x 0 + (540638143/1000000000 : ℝ)*x 1 + (-2136259193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212371013/400000000 : ℝ)^8241 ≤ (5382890321669/12500000000000 : ℝ)^6193 := by
    have hnat : (212371013 : ℕ)^8241*12500000000000^6193 ≤ 5382890321669^6193*400000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212371013 400000000 5382890321669 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540638143/1000000000 : ℝ)^8241 ≤ (22057181128631/50000000000000 : ℝ)^6193 := by
    have hnat : (540638143 : ℕ)^8241*50000000000000^6193 ≤ 22057181128631^6193*1000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540638143 1000000000 22057181128631 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136259193/10000000000 : ℝ)^8241 ≤ (6411257577301/50000000000000 : ℝ)^6193 := by
    have hnat : (2136259193 : ℕ)^8241*50000000000000^6193 ≤ 6411257577301^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136259193 10000000000 6411257577301 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212371013/400000000 : ℝ), (540638143/1000000000 : ℝ), (-2136259193/10000000000 : ℝ)] ![(5382890321669/12500000000000 : ℝ), (22057181128631/50000000000000 : ℝ), (6411257577301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212371013/400000000 : ℝ)|^8241 ≤ (5382890321669/12500000000000 : ℝ)^6193
        have hw : |(212371013/400000000 : ℝ)|=(212371013/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540638143/1000000000 : ℝ)|^8241 ≤ (22057181128631/50000000000000 : ℝ)^6193
        have hw : |(540638143/1000000000 : ℝ)|=(540638143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136259193/10000000000 : ℝ)|^8241 ≤ (6411257577301/50000000000000 : ℝ)^6193
        have hw : |(-2136259193/10000000000 : ℝ)|=(2136259193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s4_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377447109/10000000000 : ℝ)*x 0 + (2264842589/5000000000 : ℝ)*x 1 + (4230442557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377447109/10000000000 : ℝ)^8241 ≤ (33309960336697/100000000000000 : ℝ)^6193 := by
    have hnat : (4377447109 : ℕ)^8241*100000000000000^6193 ≤ 33309960336697^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377447109 10000000000 33309960336697 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264842589/5000000000 : ℝ)^8241 ≤ (4357537362079/12500000000000 : ℝ)^6193 := by
    have hnat : (2264842589 : ℕ)^8241*12500000000000^6193 ≤ 4357537362079^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264842589 5000000000 4357537362079 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230442557/10000000000 : ℝ)^8241 ≤ (31829740757417/100000000000000 : ℝ)^6193 := by
    have hnat : (4230442557 : ℕ)^8241*100000000000000^6193 ≤ 31829740757417^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230442557 10000000000 31829740757417 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377447109/10000000000 : ℝ), (2264842589/5000000000 : ℝ), (4230442557/10000000000 : ℝ)] ![(33309960336697/100000000000000 : ℝ), (4357537362079/12500000000000 : ℝ), (31829740757417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377447109/10000000000 : ℝ)|^8241 ≤ (33309960336697/100000000000000 : ℝ)^6193
        have hw : |(4377447109/10000000000 : ℝ)|=(4377447109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264842589/5000000000 : ℝ)|^8241 ≤ (4357537362079/12500000000000 : ℝ)^6193
        have hw : |(2264842589/5000000000 : ℝ)|=(2264842589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230442557/10000000000 : ℝ)|^8241 ≤ (31829740757417/100000000000000 : ℝ)^6193
        have hw : |(4230442557/10000000000 : ℝ)|=(4230442557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10983/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14247/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2067/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2067/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2067/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2067/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2067/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2067/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2067/20000 : ℝ) ^ (515/128 : ℝ) ≤ (1081782186574489/10000000000000000000 : ℝ) := by
    have hpowers : (2067/20000 : ℝ)^515 ≤ (1081782186574489/10000000000000000000 : ℝ)^128 := by
      have hnat : (2067 : ℕ)^515*10000000000000000000^128 ≤ 1081782186574489^128*20000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2067 20000 1081782186574489 10000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2067/20000 : ℝ)) (X := (1081782186574489/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14933/100000 : ℝ) ^ (515/128 : ℝ) ≤ (47558958154889419/100000000000000000000 : ℝ) := by
    have hpowers : (14933/100000 : ℝ)^515 ≤ (47558958154889419/100000000000000000000 : ℝ)^128 := by
      have hnat : (14933 : ℕ)^515*100000000000000000000^128 ≤ 47558958154889419^128*100000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14933 100000 47558958154889419 100000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14933/100000 : ℝ)) (X := (47558958154889419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001081782186574489/5000000000000000000 : ℝ) ≤ (10000537696563351/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (5001081782186574489/5000000000000000000 : ℝ)^128 ≤ (10000537696563351/10000000000000000 : ℝ)^515 := by
      have hnat : (5001081782186574489 : ℕ)^128*10000000000000000^515 ≤ 10000537696563351^515*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001081782186574489 5000000000000000000 10000537696563351 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537696563351/10000000000000000 : ℝ)) (X := (5001081782186574489/5000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058376780020634309/100000000000000000000 : ℝ) ≤ (10001450599894659/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (100058376780020634309/100000000000000000000 : ℝ)^128 ≤ (10001450599894659/10000000000000000 : ℝ)^515 := by
      have hnat : (100058376780020634309 : ℕ)^128*10000000000000000^515 ≤ 10001450599894659^515*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058376780020634309 100000000000000000000 10001450599894659 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001450599894659/10000000000000000 : ℝ)) (X := (100058376780020634309/100000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047558958154889419/50000000000000000000 : ℝ) ≤ (10002363503225967/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (50047558958154889419/50000000000000000000 : ℝ)^128 ≤ (10002363503225967/10000000000000000 : ℝ)^515 := by
      have hnat : (50047558958154889419 : ℕ)^128*10000000000000000^515 ≤ 10002363503225967^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047558958154889419 50000000000000000000 10002363503225967 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002363503225967/10000000000000000 : ℝ)) (X := (50047558958154889419/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1081782186574489/10000000000000000000 : ℝ) ≤ ((22981801308470075769/22990000000000000000 : ℝ)+2*(228225832827/114950000000000 : ℝ)*(2067/20000 : ℝ))^(515/128 : ℝ) := by
    rw [show (22981801308470075769/22990000000000000000 : ℝ)+2*(228225832827/114950000000000 : ℝ)*(2067/20000 : ℝ)=(10000537696563351/10000000000000000 : ℝ) by norm_num, show 1+2*(1081782186574489/10000000000000000000 : ℝ)=(5001081782186574489/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47558958154889419/100000000000000000000 : ℝ)+(1081782186574489/10000000000000000000 : ℝ) ≤ ((22981801308470075769/22990000000000000000 : ℝ)+(228225832827/114950000000000 : ℝ)*((14933/100000 : ℝ)+(2067/20000 : ℝ)))^(515/128 : ℝ) := by
    rw [show (22981801308470075769/22990000000000000000 : ℝ)+(228225832827/114950000000000 : ℝ)*((14933/100000 : ℝ)+(2067/20000 : ℝ))=(10001450599894659/10000000000000000 : ℝ) by norm_num, show 1+(47558958154889419/100000000000000000000 : ℝ)+(1081782186574489/10000000000000000000 : ℝ)=(100058376780020634309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47558958154889419/100000000000000000000 : ℝ) ≤ ((22981801308470075769/22990000000000000000 : ℝ)+2*(228225832827/114950000000000 : ℝ)*(14933/100000 : ℝ))^(515/128 : ℝ) := by
    rw [show (22981801308470075769/22990000000000000000 : ℝ)+2*(228225832827/114950000000000 : ℝ)*(14933/100000 : ℝ)=(10002363503225967/10000000000000000 : ℝ) by norm_num, show 1+2*(47558958154889419/100000000000000000000 : ℝ)=(50047558958154889419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22981801308470075769/22990000000000000000 : ℝ)*(X 1 0+X 2 0)+(228225832827/114950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (2067/20000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (22981801308470075769/22990000000000000000 : ℝ)) (alpha := (228225832827/114950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22981801308470075769/22990000000000000000 : ℝ)*(X 0 1+X 2 1)+(228225832827/114950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (2067/20000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (22981801308470075769/22990000000000000000 : ℝ)) (alpha := (228225832827/114950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22981801308470075769/22990000000000000000 : ℝ)*(X 0 2+X 1 2)+(228225832827/114950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (2067/20000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (22981801308470075769/22990000000000000000 : ℝ)) (alpha := (228225832827/114950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-442305523/2000000000 : ℝ)*X 0 0+(84481841/156250000 : ℝ)*X 0 1+(5252693399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674021981/5000000000 : ℝ)*X 1 0+(-572486927/2500000000 : ℝ)*X 1 1+(5252692719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337011231/2500000000 : ℝ)*X 2 0+(5252692013/10000000000 : ℝ)*X 2 1+(-2289947363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377429109/10000000000 : ℝ)*X 0 0+(845910083/2000000000 : ℝ)*X 0 1+(4530575121/10000000000 : ℝ)*X 0 2+(4377429109/10000000000 : ℝ)*X 1 0+(845910083/2000000000 : ℝ)*X 1 1+(4530575121/10000000000 : ℝ)*X 1 2+(4377429109/10000000000 : ℝ)*X 2 0+(845910083/2000000000 : ℝ)*X 2 1+(4530575121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2211535829/10000000000 : ℝ)*X 0 0+(5253147947/10000000000 : ℝ)*X 0 1+(5406381477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654637657/5000000000 : ℝ)*X 1 0+(-427251839/2000000000 : ℝ)*X 1 1+(5406381439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212371013/400000000 : ℝ)*X 2 0+(540638143/1000000000 : ℝ)*X 2 1+(-2136259193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377447109/10000000000 : ℝ)*X 0 0+(2264842589/5000000000 : ℝ)*X 0 1+(4230442557/10000000000 : ℝ)*X 0 2+(4377447109/10000000000 : ℝ)*X 1 0+(2264842589/5000000000 : ℝ)*X 1 1+(4230442557/10000000000 : ℝ)*X 1 2+(4377447109/10000000000 : ℝ)*X 2 0+(2264842589/5000000000 : ℝ)*X 2 1+(4230442557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7440664895490208190251821/7562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64117151/4000000000000 : ℝ)*(base19) + (1609342419/100000000000000 : ℝ)*(base23) + (9129661/20000000000000 : ℝ)*(lower3) + (124132503/20000000000000 : ℝ)*(upper4) + (4960979/2500000000000 : ℝ)*(lower5) + (613092219748357/12500000000000 : ℝ)*(major0) + (613092219748357/12500000000000 : ℝ)*(major1) + (613092219748357/12500000000000 : ℝ)*(major2) + (162185661599631/2500000000000 : ℝ)*(sp0) + (6487448640469819/100000000000000 : ℝ)*(sp1) + (259497945362247/4000000000000 : ℝ)*(sp2) + (3321999498090841/100000000000000 : ℝ)*(sp3) + (11889706677/50000000000000 : ℝ)*(sp4) + (1608855497/6250000000000 : ℝ)*(sp7) + (3322025239778793/100000000000000 : ℝ)*(f.failure) + (3243725121699297/50000000000000 : ℝ)*(f.sum) + (1390831903641/605000000000000000000000000 : ℝ)*base65 + (44000518635674393/15125000000000000000000000000000 : ℝ)*base68 + (10422839767424393/15125000000000000000000000000000 : ℝ)*base70 + (85395796056424393/15125000000000000000000000000000 : ℝ)*base72 + (4007552948601/605000000000000000000000000 : ℝ)*base73 + (70842677432200607/15125000000000000000000000000000 : ℝ)*base75 + (127966183760825607/15125000000000000000000000000000 : ℝ)*base77 + (185822021325299393/15125000000000000000000000000000 : ℝ)*base80 + (416810124851/151250000000000000000000000 : ℝ)*base82 + (25322207/10000000000000000000000 : ℝ)*base90 + (25322207/10000000000000000000000 : ℝ)*base92 + (25322207/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11021822157153126267204102183/1149500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248807679/12500000000000 : ℝ)*(base19) + (2140788149/100000000000000 : ℝ)*(base23) + (98394783/100000000000000 : ℝ)*(upper3) + (23432737/25000000000000 : ℝ)*(lower4) + (79446669/20000000000000 : ℝ)*(upper5) + (4933880479325931/100000000000000 : ℝ)*(major0) + (4933880479325931/100000000000000 : ℝ)*(major1) + (4933880479325931/100000000000000 : ℝ)*(major2) + (51477329473/100000000000000 : ℝ)*(sp1) + (23017222519/50000000000000 : ℝ)*(sp2) + (652599675866057/10000000000000 : ℝ)*(sp4) + (1305188658173933/20000000000000 : ℝ)*(sp5) + (6525948583427383/100000000000000 : ℝ)*(sp6) + (167088194018961/5000000000000 : ℝ)*(sp7) + (167088194018961/5000000000000 : ℝ)*(f.failure) + (652599675866057/10000000000000 : ℝ)*(f.sum) + (882962915281/2873750000000000000000000000 : ℝ)*base65 + (2326331133046134061/2299000000000000000000000000000000 : ℝ)*base68 + (187287460566134061/2299000000000000000000000000000000 : ℝ)*base70 + (11039443641019865939/2299000000000000000000000000000000 : ℝ)*base71 + (42276541219621/11495000000000000000000000000 : ℝ)*base74 + (8003835428965865939/2299000000000000000000000000000000 : ℝ)*base75 + (8313129083470865939/2299000000000000000000000000000000 : ℝ)*base77 + (8181410690147865939/2299000000000000000000000000000000 : ℝ)*base79 + (13252415992491/11495000000000000000000000000 : ℝ)*base82 + (2058039/500000000000000000000 : ℝ)*base90 + (2058039/500000000000000000000 : ℝ)*base92 + (2058039/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1048_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1048_s5_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212408741/10000000000 : ℝ)*x 0 + (5397526361/10000000000 : ℝ)*x 1 + (131535683/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212408741/10000000000 : ℝ)^8241 ≤ (2686859721933/20000000000000 : ℝ)^6193 := by
    have hnat : (2212408741 : ℕ)^8241*20000000000000^6193 ≤ 2686859721933^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212408741 10000000000 2686859721933 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397526361/10000000000 : ℝ)^8241 ≤ (11004559863337/25000000000000 : ℝ)^6193 := by
    have hnat : (5397526361 : ℕ)^8241*25000000000000^6193 ≤ 11004559863337^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397526361 10000000000 11004559863337 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131535683/250000000 : ℝ)^8241 ≤ (10636865481723/25000000000000 : ℝ)^6193 := by
    have hnat : (131535683 : ℕ)^8241*25000000000000^6193 ≤ 10636865481723^6193*250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131535683 250000000 10636865481723 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212408741/10000000000 : ℝ), (5397526361/10000000000 : ℝ), (131535683/250000000 : ℝ)] ![(2686859721933/20000000000000 : ℝ), (11004559863337/25000000000000 : ℝ), (10636865481723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212408741/10000000000 : ℝ)|^8241 ≤ (2686859721933/20000000000000 : ℝ)^6193
        have hw : |(-2212408741/10000000000 : ℝ)|=(2212408741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397526361/10000000000 : ℝ)|^8241 ≤ (11004559863337/25000000000000 : ℝ)^6193
        have hw : |(5397526361/10000000000 : ℝ)|=(5397526361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131535683/250000000 : ℝ)|^8241 ≤ (10636865481723/25000000000000 : ℝ)^6193
        have hw : |(131535683/250000000 : ℝ)|=(131535683/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s5_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672864709/5000000000 : ℝ)*x 0 + (-285188621/1250000000 : ℝ)*x 1 + (5261427327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672864709/5000000000 : ℝ)^8241 ≤ (8691404776427/20000000000000 : ℝ)^6193 := by
    have hnat : (2672864709 : ℕ)^8241*20000000000000^6193 ≤ 8691404776427^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672864709 5000000000 8691404776427 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285188621/1250000000 : ℝ)^8241 ≤ (3498878526473/25000000000000 : ℝ)^6193 := by
    have hnat : (285188621 : ℕ)^8241*25000000000000^6193 ≤ 3498878526473^6193*1250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285188621 1250000000 3498878526473 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261427327/10000000000 : ℝ)^8241 ≤ (42547462002219/100000000000000 : ℝ)^6193 := by
    have hnat : (5261427327 : ℕ)^8241*100000000000000^6193 ≤ 42547462002219^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261427327 10000000000 42547462002219 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672864709/5000000000 : ℝ), (-285188621/1250000000 : ℝ), (5261427327/10000000000 : ℝ)] ![(8691404776427/20000000000000 : ℝ), (3498878526473/25000000000000 : ℝ), (42547462002219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672864709/5000000000 : ℝ)|^8241 ≤ (8691404776427/20000000000000 : ℝ)^6193
        have hw : |(2672864709/5000000000 : ℝ)|=(2672864709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285188621/1250000000 : ℝ)|^8241 ≤ (3498878526473/25000000000000 : ℝ)^6193
        have hw : |(-285188621/1250000000 : ℝ)|=(285188621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261427327/10000000000 : ℝ)|^8241 ≤ (42547462002219/100000000000000 : ℝ)^6193
        have hw : |(5261427327/10000000000 : ℝ)|=(5261427327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s5_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345729417/10000000000 : ℝ)*x 0 + (2630713651/5000000000 : ℝ)*x 1 + (-1140754501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345729417/10000000000 : ℝ)^8241 ≤ (43457023871317/100000000000000 : ℝ)^6193 := by
    have hnat : (5345729417 : ℕ)^8241*100000000000000^6193 ≤ 43457023871317^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345729417 10000000000 43457023871317 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630713651/5000000000 : ℝ)^8241 ≤ (10636865433299/25000000000000 : ℝ)^6193 := by
    have hnat : (2630713651 : ℕ)^8241*25000000000000^6193 ≤ 10636865433299^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630713651 5000000000 10636865433299 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140754501/5000000000 : ℝ)^8241 ≤ (13995514383431/100000000000000 : ℝ)^6193 := by
    have hnat : (1140754501 : ℕ)^8241*100000000000000^6193 ≤ 13995514383431^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140754501 5000000000 13995514383431 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345729417/10000000000 : ℝ), (2630713651/5000000000 : ℝ), (-1140754501/5000000000 : ℝ)] ![(43457023871317/100000000000000 : ℝ), (10636865433299/25000000000000 : ℝ), (13995514383431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345729417/10000000000 : ℝ)|^8241 ≤ (43457023871317/100000000000000 : ℝ)^6193
        have hw : |(5345729417/10000000000 : ℝ)|=(5345729417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630713651/5000000000 : ℝ)|^8241 ≤ (10636865433299/25000000000000 : ℝ)^6193
        have hw : |(2630713651/5000000000 : ℝ)|=(2630713651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1140754501/5000000000 : ℝ)|^8241 ≤ (13995514383431/100000000000000 : ℝ)^6193
        have hw : |(-1140754501/5000000000 : ℝ)|=(1140754501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s5_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188971337/5000000000 : ℝ)*x 0 + (1061775843/2500000000 : ℝ)*x 1 + (451288579/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188971337/5000000000 : ℝ)^8241 ≤ (33314978453867/100000000000000 : ℝ)^6193 := by
    have hnat : (2188971337 : ℕ)^8241*100000000000000^6193 ≤ 33314978453867^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188971337 5000000000 33314978453867 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061775843/2500000000 : ℝ)^8241 ≤ (3199665940011/10000000000000 : ℝ)^6193 := by
    have hnat : (1061775843 : ℕ)^8241*10000000000000^6193 ≤ 3199665940011^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061775843 2500000000 3199665940011 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451288579/1000000000 : ℝ)^8241 ≤ (17344181064653/50000000000000 : ℝ)^6193 := by
    have hnat : (451288579 : ℕ)^8241*50000000000000^6193 ≤ 17344181064653^6193*1000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451288579 1000000000 17344181064653 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188971337/5000000000 : ℝ), (1061775843/2500000000 : ℝ), (451288579/1000000000 : ℝ)] ![(33314978453867/100000000000000 : ℝ), (3199665940011/10000000000000 : ℝ), (17344181064653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188971337/5000000000 : ℝ)|^8241 ≤ (33314978453867/100000000000000 : ℝ)^6193
        have hw : |(2188971337/5000000000 : ℝ)|=(2188971337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061775843/2500000000 : ℝ)|^8241 ≤ (3199665940011/10000000000000 : ℝ)^6193
        have hw : |(1061775843/2500000000 : ℝ)|=(1061775843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451288579/1000000000 : ℝ)|^8241 ≤ (17344181064653/50000000000000 : ℝ)^6193
        have hw : |(451288579/1000000000 : ℝ)|=(451288579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s5_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106207127/5000000000 : ℝ)*x 0 + (2630891229/5000000000 : ℝ)*x 1 + (337323131/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106207127/5000000000 : ℝ)^8241 ≤ (6717171578239/50000000000000 : ℝ)^6193 := by
    have hnat : (1106207127 : ℕ)^8241*50000000000000^6193 ≤ 6717171578239^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106207127 5000000000 6717171578239 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630891229/5000000000 : ℝ)^8241 ≤ (10637820894219/25000000000000 : ℝ)^6193 := by
    have hnat : (2630891229 : ℕ)^8241*25000000000000^6193 ≤ 10637820894219^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630891229 5000000000 10637820894219 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337323131/625000000 : ℝ)^8241 ≤ (44014373245933/100000000000000 : ℝ)^6193 := by
    have hnat : (337323131 : ℕ)^8241*100000000000000^6193 ≤ 44014373245933^6193*625000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337323131 625000000 44014373245933 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106207127/5000000000 : ℝ), (2630891229/5000000000 : ℝ), (337323131/625000000 : ℝ)] ![(6717171578239/50000000000000 : ℝ), (10637820894219/25000000000000 : ℝ), (44014373245933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106207127/5000000000 : ℝ)|^8241 ≤ (6717171578239/50000000000000 : ℝ)^6193
        have hw : |(-1106207127/5000000000 : ℝ)|=(1106207127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630891229/5000000000 : ℝ)|^8241 ≤ (10637820894219/25000000000000 : ℝ)^6193
        have hw : |(2630891229/5000000000 : ℝ)|=(2630891229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337323131/625000000 : ℝ)|^8241 ≤ (44014373245933/100000000000000 : ℝ)^6193
        have hw : |(337323131/625000000 : ℝ)|=(337323131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s5_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311498779/10000000000 : ℝ)*x 0 + (-429153249/2000000000 : ℝ)*x 1 + (5397169917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311498779/10000000000 : ℝ)^8241 ≤ (5385890294599/12500000000000 : ℝ)^6193 := by
    have hnat : (5311498779 : ℕ)^8241*12500000000000^6193 ≤ 5385890294599^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311498779 10000000000 5385890294599 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429153249/2000000000 : ℝ)^8241 ≤ (3224626580773/25000000000000 : ℝ)^6193 := by
    have hnat : (429153249 : ℕ)^8241*25000000000000^6193 ≤ 3224626580773^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429153249 2000000000 3224626580773 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397169917/10000000000 : ℝ)^8241 ≤ (11003592825859/25000000000000 : ℝ)^6193 := by
    have hnat : (5397169917 : ℕ)^8241*25000000000000^6193 ≤ 11003592825859^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397169917 10000000000 11003592825859 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311498779/10000000000 : ℝ), (-429153249/2000000000 : ℝ), (5397169917/10000000000 : ℝ)] ![(5385890294599/12500000000000 : ℝ), (3224626580773/25000000000000 : ℝ), (11003592825859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311498779/10000000000 : ℝ)|^8241 ≤ (5385890294599/12500000000000 : ℝ)^6193
        have hw : |(5311498779/10000000000 : ℝ)|=(5311498779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429153249/2000000000 : ℝ)|^8241 ≤ (3224626580773/25000000000000 : ℝ)^6193
        have hw : |(-429153249/2000000000 : ℝ)|=(429153249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397169917/10000000000 : ℝ)|^8241 ≤ (11003592825859/25000000000000 : ℝ)^6193
        have hw : |(5397169917/10000000000 : ℝ)|=(5397169917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s5_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655749277/5000000000 : ℝ)*x 0 + (1349292501/2500000000 : ℝ)*x 1 + (-2145766431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655749277/5000000000 : ℝ)^8241 ≤ (5385889990999/12500000000000 : ℝ)^6193 := by
    have hnat : (2655749277 : ℕ)^8241*12500000000000^6193 ≤ 5385889990999^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655749277 5000000000 5385889990999 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349292501/2500000000 : ℝ)^8241 ≤ (8802874449511/20000000000000 : ℝ)^6193 := by
    have hnat : (1349292501 : ℕ)^8241*20000000000000^6193 ≤ 8802874449511^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349292501 2500000000 8802874449511 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145766431/10000000000 : ℝ)^8241 ≤ (12898507810907/100000000000000 : ℝ)^6193 := by
    have hnat : (2145766431 : ℕ)^8241*100000000000000^6193 ≤ 12898507810907^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145766431 10000000000 12898507810907 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655749277/5000000000 : ℝ), (1349292501/2500000000 : ℝ), (-2145766431/10000000000 : ℝ)] ![(5385889990999/12500000000000 : ℝ), (8802874449511/20000000000000 : ℝ), (12898507810907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655749277/5000000000 : ℝ)|^8241 ≤ (5385889990999/12500000000000 : ℝ)^6193
        have hw : |(2655749277/5000000000 : ℝ)|=(2655749277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349292501/2500000000 : ℝ)|^8241 ≤ (8802874449511/20000000000000 : ℝ)^6193
        have hw : |(1349292501/2500000000 : ℝ)|=(1349292501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145766431/10000000000 : ℝ)|^8241 ≤ (12898507810907/100000000000000 : ℝ)^6193
        have hw : |(-2145766431/10000000000 : ℝ)|=(2145766431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s5_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094488409/2500000000 : ℝ)*x 0 + (4512192503/10000000000 : ℝ)*x 1 + (4247799607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094488409/2500000000 : ℝ)^8241 ≤ (16657544728889/50000000000000 : ℝ)^6193 := by
    have hnat : (1094488409 : ℕ)^8241*50000000000000^6193 ≤ 16657544728889^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094488409 2500000000 16657544728889 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512192503/10000000000 : ℝ)^8241 ≤ (34681271083183/100000000000000 : ℝ)^6193 := by
    have hnat : (4512192503 : ℕ)^8241*100000000000000^6193 ≤ 34681271083183^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512192503 10000000000 34681271083183 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247799607/10000000000 : ℝ)^8241 ≤ (16001819722887/50000000000000 : ℝ)^6193 := by
    have hnat : (4247799607 : ℕ)^8241*50000000000000^6193 ≤ 16001819722887^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247799607 10000000000 16001819722887 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094488409/2500000000 : ℝ), (4512192503/10000000000 : ℝ), (4247799607/10000000000 : ℝ)] ![(16657544728889/50000000000000 : ℝ), (34681271083183/100000000000000 : ℝ), (16001819722887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094488409/2500000000 : ℝ)|^8241 ≤ (16657544728889/50000000000000 : ℝ)^6193
        have hw : |(1094488409/2500000000 : ℝ)|=(1094488409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512192503/10000000000 : ℝ)|^8241 ≤ (34681271083183/100000000000000 : ℝ)^6193
        have hw : |(4512192503/10000000000 : ℝ)|=(4512192503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247799607/10000000000 : ℝ)|^8241 ≤ (16001819722887/50000000000000 : ℝ)^6193
        have hw : |(4247799607/10000000000 : ℝ)|=(4247799607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10983/100000 : ℝ) ^ (515/128 : ℝ) ≤ (6908294397678667/50000000000000000000 : ℝ) := by
    have hpowers : (10983/100000 : ℝ)^515 ≤ (6908294397678667/50000000000000000000 : ℝ)^128 := by
      have hnat : (10983 : ℕ)^515*50000000000000000000^128 ≤ 6908294397678667^128*100000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10983 100000 6908294397678667 50000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10983/100000 : ℝ)) (X := (6908294397678667/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14247/100000 : ℝ) ^ (515/128 : ℝ) ≤ (19680181269599773/50000000000000000000 : ℝ) := by
    have hpowers : (14247/100000 : ℝ)^515 ≤ (19680181269599773/50000000000000000000 : ℝ)^128 := by
      have hnat : (14247 : ℕ)^515*50000000000000000000^128 ≤ 19680181269599773^128*100000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14247 100000 19680181269599773 50000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14247/100000 : ℝ)) (X := (19680181269599773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006908294397678667/25000000000000000000 : ℝ) ≤ (5000343366947063/5000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (25006908294397678667/25000000000000000000 : ℝ)^128 ≤ (5000343366947063/5000000000000000 : ℝ)^515 := by
      have hnat : (25006908294397678667 : ℕ)^128*5000000000000000^515 ≤ 5000343366947063^515*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006908294397678667 25000000000000000000 5000343366947063 5000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000343366947063/5000000000000000 : ℝ)) (X := (25006908294397678667/25000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250664711891681961/1250000000000000000 : ℝ) ≤ (5000660707788249/5000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (1250664711891681961/1250000000000000000 : ℝ)^128 ≤ (5000660707788249/5000000000000000 : ℝ)^515 := by
      have hnat : (1250664711891681961 : ℕ)^128*5000000000000000^515 ≤ 5000660707788249^515*1250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250664711891681961 1250000000000000000 5000660707788249 5000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000660707788249/5000000000000000 : ℝ)) (X := (1250664711891681961/1250000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019680181269599773/25000000000000000000 : ℝ) ≤ (1000195609725887/1000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (25019680181269599773/25000000000000000000 : ℝ)^128 ≤ (1000195609725887/1000000000000000 : ℝ)^515 := by
      have hnat : (25019680181269599773 : ℕ)^128*1000000000000000^515 ≤ 1000195609725887^515*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019680181269599773 25000000000000000000 1000195609725887 1000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000195609725887/1000000000000000 : ℝ)) (X := (25019680181269599773/25000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6908294397678667/50000000000000000000 : ℝ) ≤ ((1359512503399810163/1360000000000000000 : ℝ)+2*(158670420593/81600000000000 : ℝ)*(10983/100000 : ℝ))^(515/128 : ℝ) := by
    rw [show (1359512503399810163/1360000000000000000 : ℝ)+2*(158670420593/81600000000000 : ℝ)*(10983/100000 : ℝ)=(5000343366947063/5000000000000000 : ℝ) by norm_num, show 1+2*(6908294397678667/50000000000000000000 : ℝ)=(25006908294397678667/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19680181269599773/50000000000000000000 : ℝ)+(6908294397678667/50000000000000000000 : ℝ) ≤ ((1359512503399810163/1360000000000000000 : ℝ)+(158670420593/81600000000000 : ℝ)*((14247/100000 : ℝ)+(10983/100000 : ℝ)))^(515/128 : ℝ) := by
    rw [show (1359512503399810163/1360000000000000000 : ℝ)+(158670420593/81600000000000 : ℝ)*((14247/100000 : ℝ)+(10983/100000 : ℝ))=(5000660707788249/5000000000000000 : ℝ) by norm_num, show 1+(19680181269599773/50000000000000000000 : ℝ)+(6908294397678667/50000000000000000000 : ℝ)=(1250664711891681961/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19680181269599773/50000000000000000000 : ℝ) ≤ ((1359512503399810163/1360000000000000000 : ℝ)+2*(158670420593/81600000000000 : ℝ)*(14247/100000 : ℝ))^(515/128 : ℝ) := by
    rw [show (1359512503399810163/1360000000000000000 : ℝ)+2*(158670420593/81600000000000 : ℝ)*(14247/100000 : ℝ)=(1000195609725887/1000000000000000 : ℝ) by norm_num, show 1+2*(19680181269599773/50000000000000000000 : ℝ)=(25019680181269599773/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1359512503399810163/1360000000000000000 : ℝ)*(X 1 0+X 2 0)+(158670420593/81600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (10983/100000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (1359512503399810163/1360000000000000000 : ℝ)) (alpha := (158670420593/81600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1359512503399810163/1360000000000000000 : ℝ)*(X 0 1+X 2 1)+(158670420593/81600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (10983/100000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (1359512503399810163/1360000000000000000 : ℝ)) (alpha := (158670420593/81600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1359512503399810163/1360000000000000000 : ℝ)*(X 0 2+X 1 2)+(158670420593/81600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (10983/100000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (1359512503399810163/1360000000000000000 : ℝ)) (alpha := (158670420593/81600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2212408741/10000000000 : ℝ)*X 0 0+(5397526361/10000000000 : ℝ)*X 0 1+(131535683/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672864709/5000000000 : ℝ)*X 1 0+(-285188621/1250000000 : ℝ)*X 1 1+(5261427327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345729417/10000000000 : ℝ)*X 2 0+(2630713651/5000000000 : ℝ)*X 2 1+(-1140754501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188971337/5000000000 : ℝ)*X 0 0+(1061775843/2500000000 : ℝ)*X 0 1+(451288579/1000000000 : ℝ)*X 0 2+(2188971337/5000000000 : ℝ)*X 1 0+(1061775843/2500000000 : ℝ)*X 1 1+(451288579/1000000000 : ℝ)*X 1 2+(2188971337/5000000000 : ℝ)*X 2 0+(1061775843/2500000000 : ℝ)*X 2 1+(451288579/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1106207127/5000000000 : ℝ)*X 0 0+(2630891229/5000000000 : ℝ)*X 0 1+(337323131/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311498779/10000000000 : ℝ)*X 1 0+(-429153249/2000000000 : ℝ)*X 1 1+(5397169917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655749277/5000000000 : ℝ)*X 2 0+(1349292501/2500000000 : ℝ)*X 2 1+(-2145766431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094488409/2500000000 : ℝ)*X 0 0+(4512192503/10000000000 : ℝ)*X 0 1+(4247799607/10000000000 : ℝ)*X 0 2+(1094488409/2500000000 : ℝ)*X 1 0+(4512192503/10000000000 : ℝ)*X 1 1+(4247799607/10000000000 : ℝ)*X 1 2+(1094488409/2500000000 : ℝ)*X 2 0+(4512192503/10000000000 : ℝ)*X 2 1+(4247799607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107993629553842620156668763/17000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1298616107/100000000000000 : ℝ)*(base19) + (1199211189/100000000000000 : ℝ)*(base23) + (26202207/50000000000000 : ℝ)*(lower2) + (18948679/10000000000000 : ℝ)*(upper3) + (64268241/100000000000000 : ℝ)*(upper5) + (1388771223844689/25000000000000 : ℝ)*(major0) + (1388771223844689/25000000000000 : ℝ)*(major1) + (1388771223844689/25000000000000 : ℝ)*(major2) + (7347626324072863/100000000000000 : ℝ)*(sp0) + (7347656777809553/100000000000000 : ℝ)*(sp1) + (734765687721447/10000000000000 : ℝ)*(sp2) + (3762492300477797/100000000000000 : ℝ)*(sp3) + (31752352797/100000000000000 : ℝ)*(sp4) + (2400262729/12500000000000 : ℝ)*(sp7) + (3762511502579629/100000000000000 : ℝ)*(f.failure) + (367382903821283/5000000000000 : ℝ)*(f.sum) + (1288572247799/340000000000000000000000000 : ℝ)*base65 + (56668557727275693/34000000000000000000000000000000 : ℝ)*base68 + (801839308145275693/34000000000000000000000000000000 : ℝ)*base70 + (388540073517275693/34000000000000000000000000000000 : ℝ)*base72 + (235789697019/340000000000000000000000000 : ℝ)*base73 + (485186399551275693/34000000000000000000000000000000 : ℝ)*base76 + (124140223941275693/34000000000000000000000000000000 : ℝ)*base78 + (48453592341275693/34000000000000000000000000000000 : ℝ)*base80 + (1589500315901/340000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (67026629/10000000000000000000000 : ℝ)*base89 + (67026629/10000000000000000000000 : ℝ)*base91 + (67026629/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105697367160628172171085679/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206145929/12500000000000 : ℝ)*(base19) + (1615191471/100000000000000 : ℝ)*(base23) + (40041829/100000000000000 : ℝ)*(upper3) + (85686919/50000000000000 : ℝ)*(lower4) + (15118209/12500000000000 : ℝ)*(upper5) + (698027472572711/12500000000000 : ℝ)*(major0) + (698027472572711/12500000000000 : ℝ)*(major1) + (698027472572711/12500000000000 : ℝ)*(major2) + (43231018321/100000000000000 : ℝ)*(sp1) + (4555527403/12500000000000 : ℝ)*(sp2) + (7386194310972901/100000000000000 : ℝ)*(sp4) + (147722988615743/2000000000000 : ℝ)*(sp5) + (7386156251562207/100000000000000 : ℝ)*(sp6) + (472780604461373/12500000000000 : ℝ)*(sp7) + (472780604461373/12500000000000 : ℝ)*(f.failure) + (7386194310972901/100000000000000 : ℝ)*(f.sum) + (5083350117077/510000000000000000000000000 : ℝ)*base66 + (1036520887613935679/51000000000000000000000000000000 : ℝ)*base67 + (303802369260064321/51000000000000000000000000000000 : ℝ)*base70 + (413277085728064321/51000000000000000000000000000000 : ℝ)*base72 + (908715615883/510000000000000000000000000 : ℝ)*base73 + (906298826331064321/51000000000000000000000000000000 : ℝ)*base76 + (241833007313935679/51000000000000000000000000000000 : ℝ)*base77 + (472677325104064321/51000000000000000000000000000000 : ℝ)*base80 + (2384036730107/510000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1699627/1250000000000000000000 : ℝ)*base90 + (1699627/1250000000000000000000 : ℝ)*base92 + (1699627/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1048_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1048_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1048_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1048_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1048_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1048_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
