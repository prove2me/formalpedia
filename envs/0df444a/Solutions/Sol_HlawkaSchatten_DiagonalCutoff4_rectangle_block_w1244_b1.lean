-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:47.219011+00:00
-- url     : https://prove2.me/submissions/b0042b09-7424-4286-aa70-5e288f0beb01

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
theorem support_rectangle_w1244_s3_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116213663/10000000000 : ℝ)*x 0 + (2709744029/5000000000 : ℝ)*x 1 + (2620383927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116213663/10000000000 : ℝ)^8437 ≤ (128637318243/1000000000000 : ℝ)^6389 := by
    have hnat : (2116213663 : ℕ)^8437*1000000000000^6389 ≤ 128637318243^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116213663 10000000000 128637318243 1000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709744029/5000000000 : ℝ)^8437 ≤ (22266314423533/50000000000000 : ℝ)^6389 := by
    have hnat : (2709744029 : ℕ)^8437*50000000000000^6389 ≤ 22266314423533^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709744029 5000000000 22266314423533 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620383927/5000000000 : ℝ)^8437 ≤ (42603639313173/100000000000000 : ℝ)^6389 := by
    have hnat : (2620383927 : ℕ)^8437*100000000000000^6389 ≤ 42603639313173^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620383927 5000000000 42603639313173 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116213663/10000000000 : ℝ), (2709744029/5000000000 : ℝ), (2620383927/5000000000 : ℝ)] ![(128637318243/1000000000000 : ℝ), (22266314423533/50000000000000 : ℝ), (42603639313173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116213663/10000000000 : ℝ)|^8437 ≤ (128637318243/1000000000000 : ℝ)^6389
        have hw : |(-2116213663/10000000000 : ℝ)|=(2116213663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709744029/5000000000 : ℝ)|^8437 ≤ (22266314423533/50000000000000 : ℝ)^6389
        have hw : |(2709744029/5000000000 : ℝ)|=(2709744029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620383927/5000000000 : ℝ)|^8437 ≤ (42603639313173/100000000000000 : ℝ)^6389
        have hw : |(2620383927/5000000000 : ℝ)|=(2620383927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s3_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675723427/5000000000 : ℝ)*x 0 + (-441476511/2000000000 : ℝ)*x 1 + (1310191993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675723427/5000000000 : ℝ)^8437 ≤ (43795794384663/100000000000000 : ℝ)^6389 := by
    have hnat : (2675723427 : ℕ)^8437*100000000000000^6389 ≤ 43795794384663^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675723427 5000000000 43795794384663 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441476511/2000000000 : ℝ)^8437 ≤ (1700070628533/12500000000000 : ℝ)^6389 := by
    have hnat : (441476511 : ℕ)^8437*12500000000000^6389 ≤ 1700070628533^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441476511 2000000000 1700070628533 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310191993/2500000000 : ℝ)^8437 ≤ (42603640579917/100000000000000 : ℝ)^6389 := by
    have hnat : (1310191993 : ℕ)^8437*100000000000000^6389 ≤ 42603640579917^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310191993 2500000000 42603640579917 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675723427/5000000000 : ℝ), (-441476511/2000000000 : ℝ), (1310191993/2500000000 : ℝ)] ![(43795794384663/100000000000000 : ℝ), (1700070628533/12500000000000 : ℝ), (42603640579917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675723427/5000000000 : ℝ)|^8437 ≤ (43795794384663/100000000000000 : ℝ)^6389
        have hw : |(2675723427/5000000000 : ℝ)|=(2675723427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441476511/2000000000 : ℝ)|^8437 ≤ (1700070628533/12500000000000 : ℝ)^6389
        have hw : |(-441476511/2000000000 : ℝ)|=(441476511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310191993/2500000000 : ℝ)|^8437 ≤ (42603640579917/100000000000000 : ℝ)^6389
        have hw : |(1310191993/2500000000 : ℝ)|=(1310191993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s3_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351446781/10000000000 : ℝ)*x 0 + (5240768413/10000000000 : ℝ)*x 1 + (-2207382069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351446781/10000000000 : ℝ)^8437 ≤ (10948948398933/25000000000000 : ℝ)^6389 := by
    have hnat : (5351446781 : ℕ)^8437*25000000000000^6389 ≤ 10948948398933^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351446781 10000000000 10948948398933 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240768413/10000000000 : ℝ)^8437 ≤ (21301822657053/50000000000000 : ℝ)^6389 := by
    have hnat : (5240768413 : ℕ)^8437*50000000000000^6389 ≤ 21301822657053^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240768413 10000000000 21301822657053 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207382069/10000000000 : ℝ)^8437 ≤ (13600561073953/100000000000000 : ℝ)^6389 := by
    have hnat : (2207382069 : ℕ)^8437*100000000000000^6389 ≤ 13600561073953^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207382069 10000000000 13600561073953 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351446781/10000000000 : ℝ), (5240768413/10000000000 : ℝ), (-2207382069/10000000000 : ℝ)] ![(10948948398933/25000000000000 : ℝ), (21301822657053/50000000000000 : ℝ), (13600561073953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351446781/10000000000 : ℝ)|^8437 ≤ (10948948398933/25000000000000 : ℝ)^6389
        have hw : |(5351446781/10000000000 : ℝ)|=(5351446781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240768413/10000000000 : ℝ)|^8437 ≤ (21301822657053/50000000000000 : ℝ)^6389
        have hw : |(5240768413/10000000000 : ℝ)|=(5240768413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207382069/10000000000 : ℝ)|^8437 ≤ (13600561073953/100000000000000 : ℝ)^6389
        have hw : |(-2207382069/10000000000 : ℝ)|=(2207382069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s3_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174404827/5000000000 : ℝ)*x 0 + (417113773/1000000000 : ℝ)*x 1 + (566727853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174404827/5000000000 : ℝ)^8437 ≤ (6660083648791/20000000000000 : ℝ)^6389 := by
    have hnat : (2174404827 : ℕ)^8437*20000000000000^6389 ≤ 6660083648791^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174404827 5000000000 6660083648791 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417113773/1000000000 : ℝ)^8437 ≤ (1969730355401/6250000000000 : ℝ)^6389 := by
    have hnat : (417113773 : ℕ)^8437*6250000000000^6389 ≤ 1969730355401^6389*1000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417113773 1000000000 1969730355401 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566727853/1250000000 : ℝ)^8437 ≤ (35183896046669/100000000000000 : ℝ)^6389 := by
    have hnat : (566727853 : ℕ)^8437*100000000000000^6389 ≤ 35183896046669^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566727853 1250000000 35183896046669 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174404827/5000000000 : ℝ), (417113773/1000000000 : ℝ), (566727853/1250000000 : ℝ)] ![(6660083648791/20000000000000 : ℝ), (1969730355401/6250000000000 : ℝ), (35183896046669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174404827/5000000000 : ℝ)|^8437 ≤ (6660083648791/20000000000000 : ℝ)^6389
        have hw : |(2174404827/5000000000 : ℝ)|=(2174404827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417113773/1000000000 : ℝ)|^8437 ≤ (1969730355401/6250000000000 : ℝ)^6389
        have hw : |(417113773/1000000000 : ℝ)|=(417113773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566727853/1250000000 : ℝ)|^8437 ≤ (35183896046669/100000000000000 : ℝ)^6389
        have hw : |(566727853/1250000000 : ℝ)|=(566727853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s3_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058113969/5000000000 : ℝ)*x 0 + (655177087/1250000000 : ℝ)*x 1 + (338677223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058113969/5000000000 : ℝ)^8437 ≤ (12863846412319/100000000000000 : ℝ)^6389 := by
    have hnat : (1058113969 : ℕ)^8437*100000000000000^6389 ≤ 12863846412319^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058113969 5000000000 12863846412319 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655177087/1250000000 : ℝ)^8437 ≤ (8522120969733/20000000000000 : ℝ)^6389 := by
    have hnat : (655177087 : ℕ)^8437*20000000000000^6389 ≤ 8522120969733^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655177087 1250000000 8522120969733 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338677223/625000000 : ℝ)^8437 ≤ (22262774362789/50000000000000 : ℝ)^6389 := by
    have hnat : (338677223 : ℕ)^8437*50000000000000^6389 ≤ 22262774362789^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338677223 625000000 22262774362789 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058113969/5000000000 : ℝ), (655177087/1250000000 : ℝ), (338677223/625000000 : ℝ)] ![(12863846412319/100000000000000 : ℝ), (8522120969733/20000000000000 : ℝ), (22262774362789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058113969/5000000000 : ℝ)|^8437 ≤ (12863846412319/100000000000000 : ℝ)^6389
        have hw : |(-1058113969/5000000000 : ℝ)|=(1058113969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655177087/1250000000 : ℝ)|^8437 ≤ (8522120969733/20000000000000 : ℝ)^6389
        have hw : |(655177087/1250000000 : ℝ)|=(655177087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338677223/625000000 : ℝ)|^8437 ≤ (22262774362789/50000000000000 : ℝ)^6389
        have hw : |(338677223/625000000 : ℝ)|=(338677223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s3_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652922533/5000000000 : ℝ)*x 0 + (-202931487/1000000000 : ℝ)*x 1 + (5418835493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652922533/5000000000 : ℝ)^8437 ≤ (8660727509867/20000000000000 : ℝ)^6389 := by
    have hnat : (2652922533 : ℕ)^8437*20000000000000^6389 ≤ 8660727509867^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652922533 5000000000 8660727509867 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202931487/1000000000 : ℝ)^8437 ≤ (6085407261899/50000000000000 : ℝ)^6389 := by
    have hnat : (202931487 : ℕ)^8437*50000000000000^6389 ≤ 6085407261899^6389*1000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202931487 1000000000 6085407261899 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418835493/10000000000 : ℝ)^8437 ≤ (22262773955887/50000000000000 : ℝ)^6389 := by
    have hnat : (5418835493 : ℕ)^8437*50000000000000^6389 ≤ 22262773955887^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418835493 10000000000 22262773955887 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652922533/5000000000 : ℝ), (-202931487/1000000000 : ℝ), (5418835493/10000000000 : ℝ)] ![(8660727509867/20000000000000 : ℝ), (6085407261899/50000000000000 : ℝ), (22262773955887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652922533/5000000000 : ℝ)|^8437 ≤ (8660727509867/20000000000000 : ℝ)^6389
        have hw : |(2652922533/5000000000 : ℝ)|=(2652922533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-202931487/1000000000 : ℝ)|^8437 ≤ (6085407261899/50000000000000 : ℝ)^6389
        have hw : |(-202931487/1000000000 : ℝ)|=(202931487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418835493/10000000000 : ℝ)|^8437 ≤ (22262773955887/50000000000000 : ℝ)^6389
        have hw : |(5418835493/10000000000 : ℝ)|=(5418835493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s3_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652922489/5000000000 : ℝ)*x 0 + (5418835583/10000000000 : ℝ)*x 1 + (-1014657433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652922489/5000000000 : ℝ)^8437 ≤ (433036366009/1000000000000 : ℝ)^6389 := by
    have hnat : (2652922489 : ℕ)^8437*1000000000000^6389 ≤ 433036366009^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652922489 5000000000 433036366009 1000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418835583/10000000000 : ℝ)^8437 ≤ (44525548888339/100000000000000 : ℝ)^6389 := by
    have hnat : (5418835583 : ℕ)^8437*100000000000000^6389 ≤ 44525548888339^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418835583 10000000000 44525548888339 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014657433/5000000000 : ℝ)^8437 ≤ (6085407246059/50000000000000 : ℝ)^6389 := by
    have hnat : (1014657433 : ℕ)^8437*50000000000000^6389 ≤ 6085407246059^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014657433 5000000000 6085407246059 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652922489/5000000000 : ℝ), (5418835583/10000000000 : ℝ), (-1014657433/5000000000 : ℝ)] ![(433036366009/1000000000000 : ℝ), (44525548888339/100000000000000 : ℝ), (6085407246059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652922489/5000000000 : ℝ)|^8437 ≤ (433036366009/1000000000000 : ℝ)^6389
        have hw : |(2652922489/5000000000 : ℝ)|=(2652922489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418835583/10000000000 : ℝ)|^8437 ≤ (44525548888339/100000000000000 : ℝ)^6389
        have hw : |(5418835583/10000000000 : ℝ)|=(5418835583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1014657433/5000000000 : ℝ)|^8437 ≤ (6085407246059/50000000000000 : ℝ)^6389
        have hw : |(-1014657433/5000000000 : ℝ)|=(1014657433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s3_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087209533/2500000000 : ℝ)*x 0 + (906501257/2000000000 : ℝ)*x 1 + (4172460939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087209533/2500000000 : ℝ)^8437 ≤ (16650353106031/50000000000000 : ℝ)^6389 := by
    have hnat : (1087209533 : ℕ)^8437*50000000000000^6389 ≤ 16650353106031^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087209533 2500000000 16650353106031 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906501257/2000000000 : ℝ)^8437 ≤ (8792601231243/25000000000000 : ℝ)^6389 := by
    have hnat : (906501257 : ℕ)^8437*25000000000000^6389 ≤ 8792601231243^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906501257 2000000000 8792601231243 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172460939/10000000000 : ℝ)^8437 ≤ (31528888847333/100000000000000 : ℝ)^6389 := by
    have hnat : (4172460939 : ℕ)^8437*100000000000000^6389 ≤ 31528888847333^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172460939 10000000000 31528888847333 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087209533/2500000000 : ℝ), (906501257/2000000000 : ℝ), (4172460939/10000000000 : ℝ)] ![(16650353106031/50000000000000 : ℝ), (8792601231243/25000000000000 : ℝ), (31528888847333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087209533/2500000000 : ℝ)|^8437 ≤ (16650353106031/50000000000000 : ℝ)^6389
        have hw : |(1087209533/2500000000 : ℝ)|=(1087209533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906501257/2000000000 : ℝ)|^8437 ≤ (8792601231243/25000000000000 : ℝ)^6389
        have hw : |(906501257/2000000000 : ℝ)|=(906501257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172460939/10000000000 : ℝ)|^8437 ≤ (31528888847333/100000000000000 : ℝ)^6389
        have hw : |(4172460939/10000000000 : ℝ)|=(4172460939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8109/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2729/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8109/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8109/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8109/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8109/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8109/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8109/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9507/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (3085939753473641/50000000000000000000 : ℝ) := by
    have hpowers : (9507/100000 : ℝ)^2109 ≤ (3085939753473641/50000000000000000000 : ℝ)^512 := by
      have hnat : (9507 : ℕ)^2109*50000000000000000000^512 ≤ 3085939753473641^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9507 100000 3085939753473641 50000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9507/100000 : ℝ)) (X := (3085939753473641/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8109/50000 : ℝ) ^ (2109/512 : ℝ) ≤ (55701612594012877/100000000000000000000 : ℝ) := by
    have hpowers : (8109/50000 : ℝ)^2109 ≤ (55701612594012877/100000000000000000000 : ℝ)^512 := by
      have hnat : (8109 : ℕ)^2109*100000000000000000000^512 ≤ 55701612594012877^512*50000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8109 50000 55701612594012877 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8109/50000 : ℝ)) (X := (55701612594012877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003085939753473641/25000000000000000000 : ℝ) ≤ (78127341049249/78125000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (25003085939753473641/25000000000000000000 : ℝ)^512 ≤ (78127341049249/78125000000000 : ℝ)^2109 := by
      have hnat : (25003085939753473641 : ℕ)^512*78125000000000^2109 ≤ 78127341049249^2109*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003085939753473641 25000000000000000000 78127341049249 78125000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78127341049249/78125000000000 : ℝ)) (X := (25003085939753473641/25000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061873492100960159/100000000000000000000 : ℝ) ≤ (2500375436336957/2500000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (100061873492100960159/100000000000000000000 : ℝ)^512 ≤ (2500375436336957/2500000000000000 : ℝ)^2109 := by
      have hnat : (100061873492100960159 : ℕ)^512*2500000000000000^2109 ≤ 2500375436336957^2109*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061873492100960159 100000000000000000000 2500375436336957 2500000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500375436336957/2500000000000000 : ℝ)) (X := (100061873492100960159/100000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055701612594012877/50000000000000000000 : ℝ) ≤ (1250337979548973/1250000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50055701612594012877/50000000000000000000 : ℝ)^512 ≤ (1250337979548973/1250000000000000 : ℝ)^2109 := by
      have hnat : (50055701612594012877 : ℕ)^512*1250000000000000^2109 ≤ 1250337979548973^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055701612594012877 50000000000000000000 1250337979548973 1250000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250337979548973/1250000000000000 : ℝ)) (X := (50055701612594012877/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3085939753473641/50000000000000000000 : ℝ) ≤ ((2795381434205146067/2796250000000000000 : ℝ)+2*(100174253663/55925000000000 : ℝ)*(9507/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (2795381434205146067/2796250000000000000 : ℝ)+2*(100174253663/55925000000000 : ℝ)*(9507/100000 : ℝ)=(78127341049249/78125000000000 : ℝ) by norm_num, show 1+2*(3085939753473641/50000000000000000000 : ℝ)=(25003085939753473641/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55701612594012877/100000000000000000000 : ℝ)+(3085939753473641/50000000000000000000 : ℝ) ≤ ((2795381434205146067/2796250000000000000 : ℝ)+(100174253663/55925000000000 : ℝ)*((8109/50000 : ℝ)+(9507/100000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (2795381434205146067/2796250000000000000 : ℝ)+(100174253663/55925000000000 : ℝ)*((8109/50000 : ℝ)+(9507/100000 : ℝ))=(2500375436336957/2500000000000000 : ℝ) by norm_num, show 1+(55701612594012877/100000000000000000000 : ℝ)+(3085939753473641/50000000000000000000 : ℝ)=(100061873492100960159/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55701612594012877/100000000000000000000 : ℝ) ≤ ((2795381434205146067/2796250000000000000 : ℝ)+2*(100174253663/55925000000000 : ℝ)*(8109/50000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (2795381434205146067/2796250000000000000 : ℝ)+2*(100174253663/55925000000000 : ℝ)*(8109/50000 : ℝ)=(1250337979548973/1250000000000000 : ℝ) by norm_num, show 1+2*(55701612594012877/100000000000000000000 : ℝ)=(50055701612594012877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2795381434205146067/2796250000000000000 : ℝ)*(X 1 0+X 2 0)+(100174253663/55925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (9507/100000 : ℝ)) (hi := (8109/50000 : ℝ)) (c := (2795381434205146067/2796250000000000000 : ℝ)) (alpha := (100174253663/55925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2795381434205146067/2796250000000000000 : ℝ)*(X 0 1+X 2 1)+(100174253663/55925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (9507/100000 : ℝ)) (hi := (8109/50000 : ℝ)) (c := (2795381434205146067/2796250000000000000 : ℝ)) (alpha := (100174253663/55925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2795381434205146067/2796250000000000000 : ℝ)*(X 0 2+X 1 2)+(100174253663/55925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (9507/100000 : ℝ)) (hi := (8109/50000 : ℝ)) (c := (2795381434205146067/2796250000000000000 : ℝ)) (alpha := (100174253663/55925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2116213663/10000000000 : ℝ)*X 0 0+(2709744029/5000000000 : ℝ)*X 0 1+(2620383927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675723427/5000000000 : ℝ)*X 1 0+(-441476511/2000000000 : ℝ)*X 1 1+(1310191993/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351446781/10000000000 : ℝ)*X 2 0+(5240768413/10000000000 : ℝ)*X 2 1+(-2207382069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174404827/5000000000 : ℝ)*X 0 0+(417113773/1000000000 : ℝ)*X 0 1+(566727853/1250000000 : ℝ)*X 0 2+(2174404827/5000000000 : ℝ)*X 1 0+(417113773/1000000000 : ℝ)*X 1 1+(566727853/1250000000 : ℝ)*X 1 2+(2174404827/5000000000 : ℝ)*X 2 0+(417113773/1000000000 : ℝ)*X 2 1+(566727853/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058113969/5000000000 : ℝ)*X 0 0+(655177087/1250000000 : ℝ)*X 0 1+(338677223/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652922533/5000000000 : ℝ)*X 1 0+(-202931487/1000000000 : ℝ)*X 1 1+(5418835493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652922489/5000000000 : ℝ)*X 2 0+(5418835583/10000000000 : ℝ)*X 2 1+(-1014657433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087209533/2500000000 : ℝ)*X 0 0+(906501257/2000000000 : ℝ)*X 0 1+(4172460939/10000000000 : ℝ)*X 0 2+(1087209533/2500000000 : ℝ)*X 1 0+(906501257/2000000000 : ℝ)*X 1 1+(4172460939/10000000000 : ℝ)*X 1 2+(1087209533/2500000000 : ℝ)*X 2 0+(906501257/2000000000 : ℝ)*X 2 1+(4172460939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29725126669095335099234637/3495312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (120293433/10000000000000 : ℝ)*(base19) + (154858289/20000000000000 : ℝ)*(base23) + (207129551/100000000000000 : ℝ)*(lower2) + (22578783/20000000000000 : ℝ)*(upper5) + (208816183276033/5000000000000 : ℝ)*(major0) + (208816183276033/5000000000000 : ℝ)*(major1) + (208816183276033/5000000000000 : ℝ)*(major2) + (5595369944941753/100000000000000 : ℝ)*(sp0) + (1398851150211161/25000000000000 : ℝ)*(sp1) + (1119081821219717/20000000000000 : ℝ)*(sp2) + (344653134355579/12500000000000 : ℝ)*(sp3) + (9983862069/25000000000000 : ℝ)*(sp4) + (815322211/20000000000000 : ℝ)*(sp5) + (12092330551/100000000000000 : ℝ)*(sp7) + (1378618583587591/50000000000000 : ℝ)*(f.failure) + (5595409880390029/100000000000000 : ℝ)*(f.sum) + (193686237943/2237000000000000000000000000 : ℝ)*base65 + (25021607142644039/13981250000000000000000000000000 : ℝ)*base68 + (120184101960231539/13981250000000000000000000000000 : ℝ)*base70 + (52349672984750289/13981250000000000000000000000000 : ℝ)*base72 + (6770907222561/2237000000000000000000000000 : ℝ)*base74 + (111449011972487789/13981250000000000000000000000000 : ℝ)*base76 + (81955672823019039/13981250000000000000000000000000 : ℝ)*base78 + (388143944073237789/13981250000000000000000000000000 : ℝ)*base80 + (11963272077/6990625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4932241/2500000000000000000000 : ℝ)*base90 + (4932241/2500000000000000000000 : ℝ)*base92 + (4932241/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85064474405833986357450201/13981250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1351351619/100000000000000 : ℝ)*(base19) + (1356546031/100000000000000 : ℝ)*(base23) + (46300441/50000000000000 : ℝ)*(upper3) + (27389561/50000000000000 : ℝ)*(lower4) + (22038659/12500000000000 : ℝ)*(upper5) + (841380632944249/20000000000000 : ℝ)*(major0) + (841380632944249/20000000000000 : ℝ)*(major1) + (841380632944249/20000000000000 : ℝ)*(major2) + (6798020679/25000000000000 : ℝ)*(sp1) + (6665188559/25000000000000 : ℝ)*(sp2) + (5636380166996317/100000000000000 : ℝ)*(sp4) + (2818175811780991/50000000000000 : ℝ)*(sp5) + (5636352149696049/100000000000000 : ℝ)*(sp6) + (694356489910021/25000000000000 : ℝ)*(sp7) + (694356489910021/25000000000000 : ℝ)*(f.failure) + (5636380166996317/100000000000000 : ℝ)*(f.sum) + (6963456445247/1118500000000000000000000000 : ℝ)*base65 + (263730150727868683/55925000000000000000000000000000 : ℝ)*base67 + (99471706030131317/55925000000000000000000000000000 : ℝ)*base70 + (523999352085268683/55925000000000000000000000000000 : ℝ)*base71 + (241715169513/139812500000000000000000000 : ℝ)*base73 + (971492266439518683/55925000000000000000000000000000 : ℝ)*base75 + (227510170460418683/55925000000000000000000000000000 : ℝ)*base77 + (1066469189440093683/55925000000000000000000000000000 : ℝ)*base79 + (148501471451/1118500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8499171/1250000000000000000000 : ℝ)*base90 + (8499171/1250000000000000000000 : ℝ)*base92 + (8499171/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1244_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8109/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2729/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1244_s4_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2648117/12500000 : ℝ)*x 0 + (215896603/400000000 : ℝ)*x 1 + (5261346751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648117/12500000 : ℝ)^8437 ≤ (2576407286507/20000000000000 : ℝ)^6389 := by
    have hnat : (2648117 : ℕ)^8437*20000000000000^6389 ≤ 2576407286507^6389*12500000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648117 12500000 2576407286507 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215896603/400000000 : ℝ)^8437 ≤ (2768329274431/6250000000000 : ℝ)^6389 := by
    have hnat : (215896603 : ℕ)^8437*6250000000000^6389 ≤ 2768329274431^6389*400000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215896603 400000000 2768329274431 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261346751/10000000000 : ℝ)^8437 ≤ (42824695170621/100000000000000 : ℝ)^6389 := by
    have hnat : (5261346751 : ℕ)^8437*100000000000000^6389 ≤ 42824695170621^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261346751 10000000000 42824695170621 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2648117/12500000 : ℝ), (215896603/400000000 : ℝ), (5261346751/10000000000 : ℝ)] ![(2576407286507/20000000000000 : ℝ), (2768329274431/6250000000000 : ℝ), (42824695170621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2648117/12500000 : ℝ)|^8437 ≤ (2576407286507/20000000000000 : ℝ)^6389
        have hw : |(-2648117/12500000 : ℝ)|=(2648117/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215896603/400000000 : ℝ)|^8437 ≤ (2768329274431/6250000000000 : ℝ)^6389
        have hw : |(215896603/400000000 : ℝ)|=(215896603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261346751/10000000000 : ℝ)|^8437 ≤ (42824695170621/100000000000000 : ℝ)^6389
        have hw : |(5261346751/10000000000 : ℝ)|=(5261346751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s4_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26729407/50000000 : ℝ)*x 0 + (-273447083/1250000000 : ℝ)*x 1 + (1052269351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26729407/50000000 : ℝ)^8437 ≤ (5466957125009/12500000000000 : ℝ)^6389 := by
    have hnat : (26729407 : ℕ)^8437*12500000000000^6389 ≤ 5466957125009^6389*50000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26729407 50000000 5466957125009 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273447083/1250000000 : ℝ)^8437 ≤ (1343964777377/10000000000000 : ℝ)^6389 := by
    have hnat : (273447083 : ℕ)^8437*10000000000000^6389 ≤ 1343964777377^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273447083 1250000000 1343964777377 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052269351/2000000000 : ℝ)^8437 ≤ (8564939042723/20000000000000 : ℝ)^6389 := by
    have hnat : (1052269351 : ℕ)^8437*20000000000000^6389 ≤ 8564939042723^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052269351 2000000000 8564939042723 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26729407/50000000 : ℝ), (-273447083/1250000000 : ℝ), (1052269351/2000000000 : ℝ)] ![(5466957125009/12500000000000 : ℝ), (1343964777377/10000000000000 : ℝ), (8564939042723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26729407/50000000 : ℝ)|^8437 ≤ (5466957125009/12500000000000 : ℝ)^6389
        have hw : |(26729407/50000000 : ℝ)|=(26729407/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273447083/1250000000 : ℝ)|^8437 ≤ (1343964777377/10000000000000 : ℝ)^6389
        have hw : |(-273447083/1250000000 : ℝ)|=(273447083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052269351/2000000000 : ℝ)|^8437 ≤ (8564939042723/20000000000000 : ℝ)^6389
        have hw : |(1052269351/2000000000 : ℝ)|=(1052269351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s4_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069176297/2000000000 : ℝ)*x 0 + (2630673313/5000000000 : ℝ)*x 1 + (-2187576721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069176297/2000000000 : ℝ)^8437 ≤ (8747131583677/20000000000000 : ℝ)^6389 := by
    have hnat : (1069176297 : ℕ)^8437*20000000000000^6389 ≤ 8747131583677^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069176297 2000000000 8747131583677 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630673313/5000000000 : ℝ)^8437 ≤ (10706173456761/25000000000000 : ℝ)^6389 := by
    have hnat : (2630673313 : ℕ)^8437*25000000000000^6389 ≤ 10706173456761^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630673313 5000000000 10706173456761 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187576721/10000000000 : ℝ)^8437 ≤ (13439648236209/100000000000000 : ℝ)^6389 := by
    have hnat : (2187576721 : ℕ)^8437*100000000000000^6389 ≤ 13439648236209^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187576721 10000000000 13439648236209 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069176297/2000000000 : ℝ), (2630673313/5000000000 : ℝ), (-2187576721/10000000000 : ℝ)] ![(8747131583677/20000000000000 : ℝ), (10706173456761/25000000000000 : ℝ), (13439648236209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069176297/2000000000 : ℝ)|^8437 ≤ (8747131583677/20000000000000 : ℝ)^6389
        have hw : |(1069176297/2000000000 : ℝ)|=(1069176297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630673313/5000000000 : ℝ)|^8437 ≤ (10706173456761/25000000000000 : ℝ)^6389
        have hw : |(2630673313/5000000000 : ℝ)|=(2630673313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187576721/10000000000 : ℝ)|^8437 ≤ (13439648236209/100000000000000 : ℝ)^6389
        have hw : |(-2187576721/10000000000 : ℝ)|=(2187576721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s4_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870035427/2000000000 : ℝ)*x 0 + (263390021/625000000 : ℝ)*x 1 + (4490371301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870035427/2000000000 : ℝ)^8437 ≤ (666284936511/2000000000000 : ℝ)^6389 := by
    have hnat : (870035427 : ℕ)^8437*2000000000000^6389 ≤ 666284936511^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870035427 2000000000 666284936511 2000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263390021/625000000 : ℝ)^8437 ≤ (31946458151307/100000000000000 : ℝ)^6389 := by
    have hnat : (263390021 : ℕ)^8437*100000000000000^6389 ≤ 31946458151307^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263390021 625000000 31946458151307 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490371301/10000000000 : ℝ)^8437 ≤ (17369647501237/50000000000000 : ℝ)^6389 := by
    have hnat : (4490371301 : ℕ)^8437*50000000000000^6389 ≤ 17369647501237^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490371301 10000000000 17369647501237 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870035427/2000000000 : ℝ), (263390021/625000000 : ℝ), (4490371301/10000000000 : ℝ)] ![(666284936511/2000000000000 : ℝ), (31946458151307/100000000000000 : ℝ), (17369647501237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870035427/2000000000 : ℝ)|^8437 ≤ (666284936511/2000000000000 : ℝ)^6389
        have hw : |(870035427/2000000000 : ℝ)|=(870035427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263390021/625000000 : ℝ)|^8437 ≤ (31946458151307/100000000000000 : ℝ)^6389
        have hw : |(263390021/625000000 : ℝ)|=(263390021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490371301/10000000000 : ℝ)|^8437 ≤ (17369647501237/50000000000000 : ℝ)^6389
        have hw : |(4490371301/10000000000 : ℝ)|=(4490371301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s4_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059249933/5000000000 : ℝ)*x 0 + (5261723303/10000000000 : ℝ)*x 1 + (269851847/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059249933/5000000000 : ℝ)^8437 ≤ (1288208674819/10000000000000 : ℝ)^6389 := by
    have hnat : (1059249933 : ℕ)^8437*10000000000000^6389 ≤ 1288208674819^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059249933 5000000000 1288208674819 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261723303/10000000000 : ℝ)^8437 ≤ (8565748525921/20000000000000 : ℝ)^6389 := by
    have hnat : (5261723303 : ℕ)^8437*20000000000000^6389 ≤ 8565748525921^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261723303 10000000000 8565748525921 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269851847/500000000 : ℝ)^8437 ≤ (44289170606807/100000000000000 : ℝ)^6389 := by
    have hnat : (269851847 : ℕ)^8437*100000000000000^6389 ≤ 44289170606807^6389*500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269851847 500000000 44289170606807 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059249933/5000000000 : ℝ), (5261723303/10000000000 : ℝ), (269851847/500000000 : ℝ)] ![(1288208674819/10000000000000 : ℝ), (8565748525921/20000000000000 : ℝ), (44289170606807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059249933/5000000000 : ℝ)|^8437 ≤ (1288208674819/10000000000000 : ℝ)^6389
        have hw : |(-1059249933/5000000000 : ℝ)|=(1059249933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261723303/10000000000 : ℝ)|^8437 ≤ (8565748525921/20000000000000 : ℝ)^6389
        have hw : |(5261723303/10000000000 : ℝ)|=(5261723303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269851847/500000000 : ℝ)|^8437 ≤ (44289170606807/100000000000000 : ℝ)^6389
        have hw : |(269851847/500000000 : ℝ)|=(269851847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s4_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311159907/10000000000 : ℝ)*x 0 + (-2051886587/10000000000 : ℝ)*x 1 + (5397036989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311159907/10000000000 : ℝ)^8437 ≤ (21680464179227/50000000000000 : ℝ)^6389 := by
    have hnat : (5311159907 : ℕ)^8437*50000000000000^6389 ≤ 21680464179227^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311159907 10000000000 21680464179227 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051886587/10000000000 : ℝ)^8437 ≤ (246998009851/2000000000000 : ℝ)^6389 := by
    have hnat : (2051886587 : ℕ)^8437*2000000000000^6389 ≤ 246998009851^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051886587 10000000000 246998009851 2000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397036989/10000000000 : ℝ)^8437 ≤ (8857834227561/20000000000000 : ℝ)^6389 := by
    have hnat : (5397036989 : ℕ)^8437*20000000000000^6389 ≤ 8857834227561^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397036989 10000000000 8857834227561 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311159907/10000000000 : ℝ), (-2051886587/10000000000 : ℝ), (5397036989/10000000000 : ℝ)] ![(21680464179227/50000000000000 : ℝ), (246998009851/2000000000000 : ℝ), (8857834227561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311159907/10000000000 : ℝ)|^8437 ≤ (21680464179227/50000000000000 : ℝ)^6389
        have hw : |(5311159907/10000000000 : ℝ)|=(5311159907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051886587/10000000000 : ℝ)|^8437 ≤ (246998009851/2000000000000 : ℝ)^6389
        have hw : |(-2051886587/10000000000 : ℝ)|=(2051886587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397036989/10000000000 : ℝ)|^8437 ≤ (8857834227561/20000000000000 : ℝ)^6389
        have hw : |(5397036989/10000000000 : ℝ)|=(5397036989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s4_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311159739/10000000000 : ℝ)*x 0 + (2698518641/5000000000 : ℝ)*x 1 + (-128242901/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311159739/10000000000 : ℝ)^8437 ≤ (5420115818403/12500000000000 : ℝ)^6389 := by
    have hnat : (5311159739 : ℕ)^8437*12500000000000^6389 ≤ 5420115818403^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311159739 10000000000 5420115818403 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698518641/5000000000 : ℝ)^8437 ≤ (4325114679/9765625000 : ℝ)^6389 := by
    have hnat : (2698518641 : ℕ)^8437*9765625000^6389 ≤ 4325114679^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698518641 5000000000 4325114679 9765625000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128242901/625000000 : ℝ)^8437 ≤ (12349899133419/100000000000000 : ℝ)^6389 := by
    have hnat : (128242901 : ℕ)^8437*100000000000000^6389 ≤ 12349899133419^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128242901 625000000 12349899133419 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311159739/10000000000 : ℝ), (2698518641/5000000000 : ℝ), (-128242901/625000000 : ℝ)] ![(5420115818403/12500000000000 : ℝ), (4325114679/9765625000 : ℝ), (12349899133419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311159739/10000000000 : ℝ)|^8437 ≤ (5420115818403/12500000000000 : ℝ)^6389
        have hw : |(5311159739/10000000000 : ℝ)|=(5311159739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698518641/5000000000 : ℝ)|^8437 ≤ (4325114679/9765625000 : ℝ)^6389
        have hw : |(2698518641/5000000000 : ℝ)|=(2698518641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128242901/625000000 : ℝ)|^8437 ≤ (12349899133419/100000000000000 : ℝ)^6389
        have hw : |(-128242901/625000000 : ℝ)|=(128242901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s4_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175094829/5000000000 : ℝ)*x 0 + (4489607251/10000000000 : ℝ)*x 1 + (843001479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175094829/5000000000 : ℝ)^8437 ≤ (6662874694037/20000000000000 : ℝ)^6389 := by
    have hnat : (2175094829 : ℕ)^8437*20000000000000^6389 ≤ 6662874694037^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175094829 5000000000 6662874694037 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489607251/10000000000 : ℝ)^8437 ≤ (8682872361619/25000000000000 : ℝ)^6389 := by
    have hnat : (4489607251 : ℕ)^8437*25000000000000^6389 ≤ 8682872361619^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489607251 10000000000 8682872361619 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843001479/2000000000 : ℝ)^8437 ≤ (15977068534529/50000000000000 : ℝ)^6389 := by
    have hnat : (843001479 : ℕ)^8437*50000000000000^6389 ≤ 15977068534529^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843001479 2000000000 15977068534529 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175094829/5000000000 : ℝ), (4489607251/10000000000 : ℝ), (843001479/2000000000 : ℝ)] ![(6662874694037/20000000000000 : ℝ), (8682872361619/25000000000000 : ℝ), (15977068534529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175094829/5000000000 : ℝ)|^8437 ≤ (6662874694037/20000000000000 : ℝ)^6389
        have hw : |(2175094829/5000000000 : ℝ)|=(2175094829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489607251/10000000000 : ℝ)|^8437 ≤ (8682872361619/25000000000000 : ℝ)^6389
        have hw : |(4489607251/10000000000 : ℝ)|=(4489607251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(843001479/2000000000 : ℝ)|^8437 ≤ (15977068534529/50000000000000 : ℝ)^6389
        have hw : |(843001479/2000000000 : ℝ)|=(843001479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2729/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2729/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2729/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2729/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2729/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2729/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2729/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2729/25000 : ℝ) ^ (2109/512 : ℝ) ≤ (10905570644520777/100000000000000000000 : ℝ) := by
    have hpowers : (2729/25000 : ℝ)^2109 ≤ (10905570644520777/100000000000000000000 : ℝ)^512 := by
      have hnat : (2729 : ℕ)^2109*100000000000000000000^512 ≤ 10905570644520777^512*25000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2729 25000 10905570644520777 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2729/25000 : ℝ)) (X := (10905570644520777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14699/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (18574251032790853/50000000000000000000 : ℝ) := by
    have hpowers : (14699/100000 : ℝ)^2109 ≤ (18574251032790853/50000000000000000000 : ℝ)^512 := by
      have hnat : (14699 : ℕ)^2109*50000000000000000000^512 ≤ 18574251032790853^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14699 100000 18574251032790853 50000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14699/100000 : ℝ)) (X := (18574251032790853/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010905570644520777/50000000000000000000 : ℝ) ≤ (2000105892671957/2000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50010905570644520777/50000000000000000000 : ℝ)^512 ≤ (2000105892671957/2000000000000000 : ℝ)^2109 := by
      have hnat : (50010905570644520777 : ℕ)^512*2000000000000000^2109 ≤ 2000105892671957^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010905570644520777 50000000000000000000 2000105892671957 2000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000105892671957/2000000000000000 : ℝ)) (X := (50010905570644520777/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048054072710102483/100000000000000000000 : ℝ) ≤ (10001166392133193/10000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (100048054072710102483/100000000000000000000 : ℝ)^512 ≤ (10001166392133193/10000000000000000 : ℝ)^2109 := by
      have hnat : (100048054072710102483 : ℕ)^512*10000000000000000^2109 ≤ 10001166392133193^2109*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048054072710102483 100000000000000000000 10001166392133193 10000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001166392133193/10000000000000000 : ℝ)) (X := (100048054072710102483/100000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018574251032790853/25000000000000000000 : ℝ) ≤ (10001803320906601/10000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (25018574251032790853/25000000000000000000 : ℝ)^512 ≤ (10001803320906601/10000000000000000 : ℝ)^2109 := by
      have hnat : (25018574251032790853 : ℕ)^512*10000000000000000^2109 ≤ 10001803320906601^2109*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018574251032790853 25000000000000000000 10001803320906601 10000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001803320906601/10000000000000000 : ℝ)) (X := (25018574251032790853/25000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10905570644520777/100000000000000000000 : ℝ) ≤ ((12606032510303007733/12610000000000000000 : ℝ)+2*(6634674723/3940625000000 : ℝ)*(2729/25000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (12606032510303007733/12610000000000000000 : ℝ)+2*(6634674723/3940625000000 : ℝ)*(2729/25000 : ℝ)=(2000105892671957/2000000000000000 : ℝ) by norm_num, show 1+2*(10905570644520777/100000000000000000000 : ℝ)=(50010905570644520777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18574251032790853/50000000000000000000 : ℝ)+(10905570644520777/100000000000000000000 : ℝ) ≤ ((12606032510303007733/12610000000000000000 : ℝ)+(6634674723/3940625000000 : ℝ)*((14699/100000 : ℝ)+(2729/25000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (12606032510303007733/12610000000000000000 : ℝ)+(6634674723/3940625000000 : ℝ)*((14699/100000 : ℝ)+(2729/25000 : ℝ))=(10001166392133193/10000000000000000 : ℝ) by norm_num, show 1+(18574251032790853/50000000000000000000 : ℝ)+(10905570644520777/100000000000000000000 : ℝ)=(100048054072710102483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18574251032790853/50000000000000000000 : ℝ) ≤ ((12606032510303007733/12610000000000000000 : ℝ)+2*(6634674723/3940625000000 : ℝ)*(14699/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (12606032510303007733/12610000000000000000 : ℝ)+2*(6634674723/3940625000000 : ℝ)*(14699/100000 : ℝ)=(10001803320906601/10000000000000000 : ℝ) by norm_num, show 1+2*(18574251032790853/50000000000000000000 : ℝ)=(25018574251032790853/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12606032510303007733/12610000000000000000 : ℝ)*(X 1 0+X 2 0)+(6634674723/3940625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (2729/25000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (12606032510303007733/12610000000000000000 : ℝ)) (alpha := (6634674723/3940625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12606032510303007733/12610000000000000000 : ℝ)*(X 0 1+X 2 1)+(6634674723/3940625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (2729/25000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (12606032510303007733/12610000000000000000 : ℝ)) (alpha := (6634674723/3940625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12606032510303007733/12610000000000000000 : ℝ)*(X 0 2+X 1 2)+(6634674723/3940625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (2729/25000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (12606032510303007733/12610000000000000000 : ℝ)) (alpha := (6634674723/3940625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2648117/12500000 : ℝ)*X 0 0+(215896603/400000000 : ℝ)*X 0 1+(5261346751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26729407/50000000 : ℝ)*X 1 0+(-273447083/1250000000 : ℝ)*X 1 1+(1052269351/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069176297/2000000000 : ℝ)*X 2 0+(2630673313/5000000000 : ℝ)*X 2 1+(-2187576721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870035427/2000000000 : ℝ)*X 0 0+(263390021/625000000 : ℝ)*X 0 1+(4490371301/10000000000 : ℝ)*X 0 2+(870035427/2000000000 : ℝ)*X 1 0+(263390021/625000000 : ℝ)*X 1 1+(4490371301/10000000000 : ℝ)*X 1 2+(870035427/2000000000 : ℝ)*X 2 0+(263390021/625000000 : ℝ)*X 2 1+(4490371301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059249933/5000000000 : ℝ)*X 0 0+(5261723303/10000000000 : ℝ)*X 0 1+(269851847/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311159907/10000000000 : ℝ)*X 1 0+(-2051886587/10000000000 : ℝ)*X 1 1+(5397036989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311159739/10000000000 : ℝ)*X 2 0+(2698518641/5000000000 : ℝ)*X 2 1+(-128242901/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175094829/5000000000 : ℝ)*X 0 0+(4489607251/10000000000 : ℝ)*X 0 1+(843001479/2000000000 : ℝ)*X 0 2+(2175094829/5000000000 : ℝ)*X 1 0+(4489607251/10000000000 : ℝ)*X 1 1+(843001479/2000000000 : ℝ)*X 1 2+(2175094829/5000000000 : ℝ)*X 2 0+(4489607251/10000000000 : ℝ)*X 2 1+(843001479/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38271083130641040669867/6305000000000000000000000000 : ℝ) := by norm_num
    linear_combination (342161679/25000000000000 : ℝ)*(base19) + (688707073/50000000000000 : ℝ)*(base23) + (123768751/50000000000000 : ℝ)*(upper3) + (57782179/100000000000000 : ℝ)*(upper4) + (20872137/20000000000000 : ℝ)*(upper5) + (1371351998533227/25000000000000 : ℝ)*(major0) + (1371351998533227/25000000000000 : ℝ)*(major1) + (1371351998533227/25000000000000 : ℝ)*(major2) + (367464125451837/5000000000000 : ℝ)*(sp0) + (3674655455443733/50000000000000 : ℝ)*(sp1) + (1469862180424007/20000000000000 : ℝ)*(sp2) + (3621484822117803/100000000000000 : ℝ)*(sp3) + (29770497441/100000000000000 : ℝ)*(sp4) + (18684281897/100000000000000 : ℝ)*(sp7) + (36215035063997/1000000000000 : ℝ)*(f.failure) + (3674656139767091/50000000000000 : ℝ)*(f.sum) + (22950706007637/6305000000000000000000000000 : ℝ)*base66 + (3363789945436144391/315250000000000000000000000000000 : ℝ)*base67 + (506642189418855609/315250000000000000000000000000000 : ℝ)*base70 + (5165939283252894391/315250000000000000000000000000000 : ℝ)*base71 + (33590360759467/6305000000000000000000000000 : ℝ)*base74 + (4295370455306355609/315250000000000000000000000000000 : ℝ)*base76 + (8201317737234144391/315250000000000000000000000000000 : ℝ)*base77 + (3249470579665605609/315250000000000000000000000000000 : ℝ)*base80 + (33240125903327/6305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (134453/50000000000000000000 : ℝ)*base89 + (134453/50000000000000000000 : ℝ)*base91 + (134453/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43167704615103482327247/6305000000000000000000000000 : ℝ) := by norm_num
    linear_combination (959125249/100000000000000 : ℝ)*(base19) + (1092702773/100000000000000 : ℝ)*(base23) + (30780543/25000000000000 : ℝ)*(upper2) + (328696719/100000000000000 : ℝ)*(upper3) + (154169723/100000000000000 : ℝ)*(upper5) + (5515944961807599/100000000000000 : ℝ)*(major0) + (5515944961807599/100000000000000 : ℝ)*(major1) + (5515944961807599/100000000000000 : ℝ)*(major2) + (10980686359/100000000000000 : ℝ)*(sp1) + (7927693161/25000000000000 : ℝ)*(sp2) + (7390225476132591/100000000000000 : ℝ)*(sp4) + (3695106768160491/50000000000000 : ℝ)*(sp5) + (7390192672657173/100000000000000 : ℝ)*(sp6) + (910416054815793/25000000000000 : ℝ)*(sp7) + (910416054815793/25000000000000 : ℝ)*(f.failure) + (7390225476132591/100000000000000 : ℝ)*(f.sum) + (10794131900193/3152500000000000000000000000 : ℝ)*base66 + (3116366749456563067/1261000000000000000000000000000000 : ℝ)*base67 + (9705910286878436933/1261000000000000000000000000000000 : ℝ)*base70 + (13812498872951563067/1261000000000000000000000000000000 : ℝ)*base71 + (14547166867527/3152500000000000000000000000 : ℝ)*base73 + (3985140039361436933/1261000000000000000000000000000000 : ℝ)*base76 + (10914515439658563067/1261000000000000000000000000000000 : ℝ)*base77 + (20421150125220436933/1261000000000000000000000000000000 : ℝ)*base80 + (812181226647/788125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2377257/1250000000000000000000 : ℝ)*base89 + (2377257/1250000000000000000000 : ℝ)*base91 + (2377257/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1244_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2729/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1244_s5_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059469651/5000000000 : ℝ)*x 0 + (5392361517/10000000000 : ℝ)*x 1 + (1316526851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059469651/5000000000 : ℝ)^8437 ≤ (3221403878851/25000000000000 : ℝ)^6389 := by
    have hnat : (1059469651 : ℕ)^8437*25000000000000^6389 ≤ 3221403878851^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059469651 5000000000 3221403878851 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392361517/10000000000 : ℝ)^8437 ≤ (22119255727691/50000000000000 : ℝ)^6389 := by
    have hnat : (5392361517 : ℕ)^8437*50000000000000^6389 ≤ 22119255727691^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392361517 10000000000 22119255727691 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316526851/2500000000 : ℝ)^8437 ≤ (21437936508637/50000000000000 : ℝ)^6389 := by
    have hnat : (1316526851 : ℕ)^8437*50000000000000^6389 ≤ 21437936508637^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316526851 2500000000 21437936508637 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059469651/5000000000 : ℝ), (5392361517/10000000000 : ℝ), (1316526851/2500000000 : ℝ)] ![(3221403878851/25000000000000 : ℝ), (22119255727691/50000000000000 : ℝ), (21437936508637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059469651/5000000000 : ℝ)|^8437 ≤ (3221403878851/25000000000000 : ℝ)^6389
        have hw : |(-1059469651/5000000000 : ℝ)|=(1059469651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392361517/10000000000 : ℝ)|^8437 ≤ (22119255727691/50000000000000 : ℝ)^6389
        have hw : |(5392361517/10000000000 : ℝ)|=(5392361517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316526851/2500000000 : ℝ)|^8437 ≤ (21437936508637/50000000000000 : ℝ)^6389
        have hw : |(1316526851/2500000000 : ℝ)|=(1316526851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s5_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344602637/10000000000 : ℝ)*x 0 + (-1091484877/5000000000 : ℝ)*x 1 + (2633053707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344602637/10000000000 : ℝ)^8437 ≤ (2186092109519/5000000000000 : ℝ)^6389 := by
    have hnat : (5344602637 : ℕ)^8437*5000000000000^6389 ≤ 2186092109519^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344602637 10000000000 2186092109519 5000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091484877/5000000000 : ℝ)^8437 ≤ (2680456936317/20000000000000 : ℝ)^6389 := by
    have hnat : (1091484877 : ℕ)^8437*20000000000000^6389 ≤ 2680456936317^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091484877 5000000000 2680456936317 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633053707/5000000000 : ℝ)^8437 ≤ (42875873124791/100000000000000 : ℝ)^6389 := by
    have hnat : (2633053707 : ℕ)^8437*100000000000000^6389 ≤ 42875873124791^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633053707 5000000000 42875873124791 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344602637/10000000000 : ℝ), (-1091484877/5000000000 : ℝ), (2633053707/5000000000 : ℝ)] ![(2186092109519/5000000000000 : ℝ), (2680456936317/20000000000000 : ℝ), (42875873124791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344602637/10000000000 : ℝ)|^8437 ≤ (2186092109519/5000000000000 : ℝ)^6389
        have hw : |(5344602637/10000000000 : ℝ)|=(5344602637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091484877/5000000000 : ℝ)|^8437 ≤ (2680456936317/20000000000000 : ℝ)^6389
        have hw : |(-1091484877/5000000000 : ℝ)|=(1091484877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633053707/5000000000 : ℝ)|^8437 ≤ (42875873124791/100000000000000 : ℝ)^6389
        have hw : |(2633053707/5000000000 : ℝ)|=(2633053707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s5_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344602947/10000000000 : ℝ)*x 0 + (5266107351/10000000000 : ℝ)*x 1 + (-136435589/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344602947/10000000000 : ℝ)^8437 ≤ (43721845539263/100000000000000 : ℝ)^6389 := by
    have hnat : (5344602947 : ℕ)^8437*100000000000000^6389 ≤ 43721845539263^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344602947 10000000000 43721845539263 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266107351/10000000000 : ℝ)^8437 ≤ (5359484055929/12500000000000 : ℝ)^6389 := by
    have hnat : (5266107351 : ℕ)^8437*12500000000000^6389 ≤ 5359484055929^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266107351 10000000000 5359484055929 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136435589/625000000 : ℝ)^8437 ≤ (6701141003057/50000000000000 : ℝ)^6389 := by
    have hnat : (136435589 : ℕ)^8437*50000000000000^6389 ≤ 6701141003057^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136435589 625000000 6701141003057 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344602947/10000000000 : ℝ), (5266107351/10000000000 : ℝ), (-136435589/625000000 : ℝ)] ![(43721845539263/100000000000000 : ℝ), (5359484055929/12500000000000 : ℝ), (6701141003057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344602947/10000000000 : ℝ)|^8437 ≤ (43721845539263/100000000000000 : ℝ)^6389
        have hw : |(5344602947/10000000000 : ℝ)|=(5344602947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266107351/10000000000 : ℝ)|^8437 ≤ (5359484055929/12500000000000 : ℝ)^6389
        have hw : |(5266107351/10000000000 : ℝ)|=(5266107351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136435589/625000000 : ℝ)|^8437 ≤ (6701141003057/50000000000000 : ℝ)^6389
        have hw : |(-136435589/625000000 : ℝ)|=(136435589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s5_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175219667/5000000000 : ℝ)*x 0 + (4224165591/10000000000 : ℝ)*x 1 + (4480379143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175219667/5000000000 : ℝ)^8437 ≤ (8329224614683/25000000000000 : ℝ)^6389 := by
    have hnat : (2175219667 : ℕ)^8437*25000000000000^6389 ≤ 8329224614683^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175219667 5000000000 8329224614683 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224165591/10000000000 : ℝ)^8437 ≤ (32045853043751/100000000000000 : ℝ)^6389 := by
    have hnat : (4224165591 : ℕ)^8437*100000000000000^6389 ≤ 32045853043751^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224165591 10000000000 32045853043751 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480379143/10000000000 : ℝ)^8437 ≤ (2164828030093/6250000000000 : ℝ)^6389 := by
    have hnat : (4480379143 : ℕ)^8437*6250000000000^6389 ≤ 2164828030093^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480379143 10000000000 2164828030093 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175219667/5000000000 : ℝ), (4224165591/10000000000 : ℝ), (4480379143/10000000000 : ℝ)] ![(8329224614683/25000000000000 : ℝ), (32045853043751/100000000000000 : ℝ), (2164828030093/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175219667/5000000000 : ℝ)|^8437 ≤ (8329224614683/25000000000000 : ℝ)^6389
        have hw : |(2175219667/5000000000 : ℝ)|=(2175219667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224165591/10000000000 : ℝ)|^8437 ≤ (32045853043751/100000000000000 : ℝ)^6389
        have hw : |(4224165591/10000000000 : ℝ)|=(4224165591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480379143/10000000000 : ℝ)|^8437 ≤ (2164828030093/6250000000000 : ℝ)^6389
        have hw : |(4480379143/10000000000 : ℝ)|=(4480379143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s5_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118944281/10000000000 : ℝ)*x 0 + (5266431921/10000000000 : ℝ)*x 1 + (2696017879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118944281/10000000000 : ℝ)^8437 ≤ (12885655499207/100000000000000 : ℝ)^6389 := by
    have hnat : (2118944281 : ℕ)^8437*100000000000000^6389 ≤ 12885655499207^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118944281 10000000000 12885655499207 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266431921/10000000000 : ℝ)^8437 ≤ (85758724343/200000000000 : ℝ)^6389 := by
    have hnat : (5266431921 : ℕ)^8437*200000000000^6389 ≤ 85758724343^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266431921 10000000000 85758724343 200000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696017879/5000000000 : ℝ)^8437 ≤ (44234982315409/100000000000000 : ℝ)^6389 := by
    have hnat : (2696017879 : ℕ)^8437*100000000000000^6389 ≤ 44234982315409^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696017879 5000000000 44234982315409 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118944281/10000000000 : ℝ), (5266431921/10000000000 : ℝ), (2696017879/5000000000 : ℝ)] ![(12885655499207/100000000000000 : ℝ), (85758724343/200000000000 : ℝ), (44234982315409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118944281/10000000000 : ℝ)|^8437 ≤ (12885655499207/100000000000000 : ℝ)^6389
        have hw : |(-2118944281/10000000000 : ℝ)|=(2118944281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266431921/10000000000 : ℝ)|^8437 ≤ (85758724343/200000000000 : ℝ)^6389
        have hw : |(5266431921/10000000000 : ℝ)|=(5266431921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696017879/5000000000 : ℝ)|^8437 ≤ (44234982315409/100000000000000 : ℝ)^6389
        have hw : |(2696017879/5000000000 : ℝ)|=(2696017879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s5_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312384279/10000000000 : ℝ)*x 0 + (-1028520619/5000000000 : ℝ)*x 1 + (539203593/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312384279/10000000000 : ℝ)^8437 ≤ (43374128962059/100000000000000 : ℝ)^6389 := by
    have hnat : (5312384279 : ℕ)^8437*100000000000000^6389 ≤ 43374128962059^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312384279 10000000000 43374128962059 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028520619/5000000000 : ℝ)^8437 ≤ (12390886844151/100000000000000 : ℝ)^6389 := by
    have hnat : (1028520619 : ℕ)^8437*100000000000000^6389 ≤ 12390886844151^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028520619 5000000000 12390886844151 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539203593/1000000000 : ℝ)^8437 ≤ (44234984178769/100000000000000 : ℝ)^6389 := by
    have hnat : (539203593 : ℕ)^8437*100000000000000^6389 ≤ 44234984178769^6389*1000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539203593 1000000000 44234984178769 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312384279/10000000000 : ℝ), (-1028520619/5000000000 : ℝ), (539203593/1000000000 : ℝ)] ![(43374128962059/100000000000000 : ℝ), (12390886844151/100000000000000 : ℝ), (44234984178769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312384279/10000000000 : ℝ)|^8437 ≤ (43374128962059/100000000000000 : ℝ)^6389
        have hw : |(5312384279/10000000000 : ℝ)|=(5312384279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028520619/5000000000 : ℝ)|^8437 ≤ (12390886844151/100000000000000 : ℝ)^6389
        have hw : |(-1028520619/5000000000 : ℝ)|=(1028520619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539203593/1000000000 : ℝ)|^8437 ≤ (44234984178769/100000000000000 : ℝ)^6389
        have hw : |(539203593/1000000000 : ℝ)|=(539203593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s5_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328096119/2500000000 : ℝ)*x 0 + (5392035867/10000000000 : ℝ)*x 1 + (-1028520529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328096119/2500000000 : ℝ)^8437 ≤ (43374131086099/100000000000000 : ℝ)^6389 := by
    have hnat : (1328096119 : ℕ)^8437*100000000000000^6389 ≤ 43374131086099^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328096119 2500000000 43374131086099 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392035867/10000000000 : ℝ)^8437 ≤ (44234983496259/100000000000000 : ℝ)^6389 := by
    have hnat : (5392035867 : ℕ)^8437*100000000000000^6389 ≤ 44234983496259^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392035867 10000000000 44234983496259 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028520529/5000000000 : ℝ)^8437 ≤ (774430338271/6250000000000 : ℝ)^6389 := by
    have hnat : (1028520529 : ℕ)^8437*6250000000000^6389 ≤ 774430338271^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028520529 5000000000 774430338271 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328096119/2500000000 : ℝ), (5392035867/10000000000 : ℝ), (-1028520529/5000000000 : ℝ)] ![(43374131086099/100000000000000 : ℝ), (44234983496259/100000000000000 : ℝ), (774430338271/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328096119/2500000000 : ℝ)|^8437 ≤ (43374131086099/100000000000000 : ℝ)^6389
        have hw : |(1328096119/2500000000 : ℝ)|=(1328096119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392035867/10000000000 : ℝ)|^8437 ≤ (44234983496259/100000000000000 : ℝ)^6389
        have hw : |(5392035867/10000000000 : ℝ)|=(5392035867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028520529/5000000000 : ℝ)|^8437 ≤ (774430338271/6250000000000 : ℝ)^6389
        have hw : |(-1028520529/5000000000 : ℝ)|=(1028520529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s5_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (135951543/312500000 : ℝ)*x 0 + (223986051/500000000 : ℝ)*x 1 + (844965217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135951543/312500000 : ℝ)^8437 ≤ (33317000015059/100000000000000 : ℝ)^6389 := by
    have hnat : (135951543 : ℕ)^8437*100000000000000^6389 ≤ 33317000015059^6389*312500000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135951543 312500000 33317000015059 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223986051/500000000 : ℝ)^8437 ≤ (17315264926531/50000000000000 : ℝ)^6389 := by
    have hnat : (223986051 : ℕ)^8437*50000000000000^6389 ≤ 17315264926531^6389*500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223986051 500000000 17315264926531 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844965217/2000000000 : ℝ)^8437 ≤ (32052470115187/100000000000000 : ℝ)^6389 := by
    have hnat : (844965217 : ℕ)^8437*100000000000000^6389 ≤ 32052470115187^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844965217 2000000000 32052470115187 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135951543/312500000 : ℝ), (223986051/500000000 : ℝ), (844965217/2000000000 : ℝ)] ![(33317000015059/100000000000000 : ℝ), (17315264926531/50000000000000 : ℝ), (32052470115187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135951543/312500000 : ℝ)|^8437 ≤ (33317000015059/100000000000000 : ℝ)^6389
        have hw : |(135951543/312500000 : ℝ)|=(135951543/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223986051/500000000 : ℝ)|^8437 ≤ (17315264926531/50000000000000 : ℝ)^6389
        have hw : |(223986051/500000000 : ℝ)|=(223986051/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844965217/2000000000 : ℝ)|^8437 ≤ (32052470115187/100000000000000 : ℝ)^6389
        have hw : |(844965217/2000000000 : ℝ)|=(844965217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (358/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14131/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/20000 : ℝ) ^ (2109/512 : ℝ) ≤ (3207177290423807/25000000000000000000 : ℝ) := by
    have hpowers : (2271/20000 : ℝ)^2109 ≤ (3207177290423807/25000000000000000000 : ℝ)^512 := by
      have hnat : (2271 : ℕ)^2109*25000000000000000000^512 ≤ 3207177290423807^512*20000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 20000 3207177290423807 25000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/20000 : ℝ)) (X := (3207177290423807/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (407119310510347/1250000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^2109 ≤ (407119310510347/1250000000000000000 : ℝ)^512 := by
      have hnat : (14237 : ℕ)^2109*1250000000000000000^512 ≤ 407119310510347^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 407119310510347 1250000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (407119310510347/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503207177290423807/12500000000000000000 : ℝ) ≤ (250015570557427/250000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (12503207177290423807/12500000000000000000 : ℝ)^512 ≤ (250015570557427/250000000000000 : ℝ)^2109 := by
      have hnat : (12503207177290423807 : ℕ)^512*250000000000000^2109 ≤ 250015570557427^2109*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503207177290423807 12500000000000000000 250015570557427 250000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250015570557427/250000000000000 : ℝ)) (X := (12503207177290423807/12500000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011349563500630747/25000000000000000000 : ℝ) ≤ (5000550969934497/5000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (25011349563500630747/25000000000000000000 : ℝ)^512 ≤ (5000550969934497/5000000000000000 : ℝ)^2109 := by
      have hnat : (25011349563500630747 : ℕ)^512*5000000000000000^2109 ≤ 5000550969934497^2109*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011349563500630747 25000000000000000000 5000550969934497 5000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000550969934497/5000000000000000 : ℝ)) (X := (25011349563500630747/25000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (625407119310510347/625000000000000000 : ℝ) ≤ (2500395264360227/2500000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (625407119310510347/625000000000000000 : ℝ)^512 ≤ (2500395264360227/2500000000000000 : ℝ)^2109 := by
      have hnat : (625407119310510347 : ℕ)^512*2500000000000000^2109 ≤ 2500395264360227^2109*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625407119310510347 625000000000000000 2500395264360227 2500000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500395264360227/2500000000000000 : ℝ)) (X := (625407119310510347/625000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3207177290423807/25000000000000000000 : ℝ) ≤ ((1440545710690100881/1441000000000000000 : ℝ)+2*(239558785957/144100000000000 : ℝ)*(2271/20000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (1440545710690100881/1441000000000000000 : ℝ)+2*(239558785957/144100000000000 : ℝ)*(2271/20000 : ℝ)=(250015570557427/250000000000000 : ℝ) by norm_num, show 1+2*(3207177290423807/25000000000000000000 : ℝ)=(12503207177290423807/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(407119310510347/1250000000000000000 : ℝ)+(3207177290423807/25000000000000000000 : ℝ) ≤ ((1440545710690100881/1441000000000000000 : ℝ)+(239558785957/144100000000000 : ℝ)*((14237/100000 : ℝ)+(2271/20000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (1440545710690100881/1441000000000000000 : ℝ)+(239558785957/144100000000000 : ℝ)*((14237/100000 : ℝ)+(2271/20000 : ℝ))=(5000550969934497/5000000000000000 : ℝ) by norm_num, show 1+(407119310510347/1250000000000000000 : ℝ)+(3207177290423807/25000000000000000000 : ℝ)=(25011349563500630747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(407119310510347/1250000000000000000 : ℝ) ≤ ((1440545710690100881/1441000000000000000 : ℝ)+2*(239558785957/144100000000000 : ℝ)*(14237/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (1440545710690100881/1441000000000000000 : ℝ)+2*(239558785957/144100000000000 : ℝ)*(14237/100000 : ℝ)=(2500395264360227/2500000000000000 : ℝ) by norm_num, show 1+2*(407119310510347/1250000000000000000 : ℝ)=(625407119310510347/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1440545710690100881/1441000000000000000 : ℝ)*(X 1 0+X 2 0)+(239558785957/144100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1440545710690100881/1441000000000000000 : ℝ)) (alpha := (239558785957/144100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1440545710690100881/1441000000000000000 : ℝ)*(X 0 1+X 2 1)+(239558785957/144100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1440545710690100881/1441000000000000000 : ℝ)) (alpha := (239558785957/144100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1440545710690100881/1441000000000000000 : ℝ)*(X 0 2+X 1 2)+(239558785957/144100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1440545710690100881/1441000000000000000 : ℝ)) (alpha := (239558785957/144100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1059469651/5000000000 : ℝ)*X 0 0+(5392361517/10000000000 : ℝ)*X 0 1+(1316526851/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344602637/10000000000 : ℝ)*X 1 0+(-1091484877/5000000000 : ℝ)*X 1 1+(2633053707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344602947/10000000000 : ℝ)*X 2 0+(5266107351/10000000000 : ℝ)*X 2 1+(-136435589/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175219667/5000000000 : ℝ)*X 0 0+(4224165591/10000000000 : ℝ)*X 0 1+(4480379143/10000000000 : ℝ)*X 0 2+(2175219667/5000000000 : ℝ)*X 1 0+(4224165591/10000000000 : ℝ)*X 1 1+(4480379143/10000000000 : ℝ)*X 1 2+(2175219667/5000000000 : ℝ)*X 2 0+(4224165591/10000000000 : ℝ)*X 2 1+(4480379143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2118944281/10000000000 : ℝ)*X 0 0+(5266431921/10000000000 : ℝ)*X 0 1+(2696017879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312384279/10000000000 : ℝ)*X 1 0+(-1028520619/5000000000 : ℝ)*X 1 1+(539203593/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328096119/2500000000 : ℝ)*X 2 0+(5392035867/10000000000 : ℝ)*X 2 1+(-1028520529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((135951543/312500000 : ℝ)*X 0 0+(223986051/500000000 : ℝ)*X 0 1+(844965217/2000000000 : ℝ)*X 0 2+(135951543/312500000 : ℝ)*X 1 0+(223986051/500000000 : ℝ)*X 1 1+(844965217/2000000000 : ℝ)*X 1 2+(135951543/312500000 : ℝ)*X 2 0+(223986051/500000000 : ℝ)*X 2 1+(844965217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19772825378025273392387799/1801250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36659187/2000000000000 : ℝ)*(base19) + (430736447/20000000000000 : ℝ)*(base23) + (356971/400000000000 : ℝ)*(lower2) + (379288109/100000000000000 : ℝ)*(upper5) + (295592471449657/5000000000000 : ℝ)*(major0) + (295592471449657/5000000000000 : ℝ)*(major1) + (295592471449657/5000000000000 : ℝ)*(major2) + (3960290618561041/50000000000000 : ℝ)*(sp0) + (7920648937669097/100000000000000 : ℝ)*(sp1) + (3960326654361519/50000000000000 : ℝ)*(sp2) + (3903020630365699/100000000000000 : ℝ)*(sp3) + (74225283191/100000000000000 : ℝ)*(sp4) + (2345888413/50000000000000 : ℝ)*(sp5) + (11199652987/50000000000000 : ℝ)*(sp7) + (3903043029671673/100000000000000 : ℝ)*(f.failure) + (7920655462405273/100000000000000 : ℝ)*(f.sum) + (5449571510541/1441000000000000000000000000 : ℝ)*base65 + (213537210679907/55000000000000000000000000000 : ℝ)*base67 + (149231663934907/55000000000000000000000000000 : ℝ)*base69 + (89665713534907/55000000000000000000000000000 : ℝ)*base71 + (1693414489587/1441000000000000000000000000 : ℝ)*base74 + (825549920174907/55000000000000000000000000000 : ℝ)*base75 + (407397097669907/55000000000000000000000000000 : ℝ)*base77 + (538862461135093/55000000000000000000000000000 : ℝ)*base80 + (2644134085039/1441000000000000000000000000 : ℝ)*base82 + (2559377/5000000000000000000000 : ℝ)*base89 + (2559377/5000000000000000000000 : ℝ)*base91 + (2559377/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (457155144003479962507565529/72050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (412055507/50000000000000 : ℝ)*(base19) + (1298067527/100000000000000 : ℝ)*(base23) + (181016727/100000000000000 : ℝ)*(upper3) + (6443057/20000000000000 : ℝ)*(lower4) + (20489777/25000000000000 : ℝ)*(upper5) + (5942363720416797/100000000000000 : ℝ)*(major0) + (5942363720416797/100000000000000 : ℝ)*(major1) + (5942363720416797/100000000000000 : ℝ)*(major2) + (1332776483/5000000000000 : ℝ)*(sp1) + (9224899783/20000000000000 : ℝ)*(sp2) + (7961538457813911/100000000000000 : ℝ)*(sp4) + (7961510978173237/100000000000000 : ℝ)*(sp5) + (7961491035247471/100000000000000 : ℝ)*(sp6) + (1961594385760321/50000000000000 : ℝ)*(sp7) + (1961594385760321/50000000000000 : ℝ)*(f.failure) + (7961538457813911/100000000000000 : ℝ)*(f.sum) + (569805299869/1801250000000000000000000000 : ℝ)*base66 + (4082367834222047/1100000000000000000000000000000 : ℝ)*base67 + (21409976773522047/1100000000000000000000000000000 : ℝ)*base69 + (2006600836177953/1100000000000000000000000000000 : ℝ)*base72 + (3483932983959/7205000000000000000000000000 : ℝ)*base73 + (28373554150322047/1100000000000000000000000000000 : ℝ)*base75 + (13480400190022047/1100000000000000000000000000000 : ℝ)*base77 + (17431227005877953/1100000000000000000000000000000 : ℝ)*base80 + (36992489480869/7205000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base87 + (24194471/2500000000000000000000 : ℝ)*base90 + (24194471/2500000000000000000000 : ℝ)*base92 + (24194471/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1244_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1244_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8109/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1244_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1244_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1244_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8109/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
