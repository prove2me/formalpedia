-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:20.002702+00:00
-- url     : https://prove2.me/submissions/071bffe7-300e-4c80-b770-16cdef0cedb3

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
theorem support_rectangle_w1185_box_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-505249799/2500000000 : ℝ)*x 0 + (5375689523/10000000000 : ℝ)*x 1 + (1343922167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505249799/2500000000 : ℝ)^4189 ≤ (481892204489/4000000000000 : ℝ)^3165 := by
    have hnat : (505249799 : ℕ)^4189*4000000000000^3165 ≤ 481892204489^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505249799 2500000000 481892204489 4000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375689523/10000000000 : ℝ)^4189 ≤ (21988176032599/50000000000000 : ℝ)^3165 := by
    have hnat : (5375689523 : ℕ)^4189*50000000000000^3165 ≤ 21988176032599^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375689523 10000000000 21988176032599 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343922167/2500000000 : ℝ)^4189 ≤ (1759053712313/4000000000000 : ℝ)^3165 := by
    have hnat : (1343922167 : ℕ)^4189*4000000000000^3165 ≤ 1759053712313^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343922167 2500000000 1759053712313 4000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505249799/2500000000 : ℝ), (5375689523/10000000000 : ℝ), (1343922167/2500000000 : ℝ)] ![(481892204489/4000000000000 : ℝ), (21988176032599/50000000000000 : ℝ), (1759053712313/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505249799/2500000000 : ℝ)|^4189 ≤ (481892204489/4000000000000 : ℝ)^3165
        have hw : |(-505249799/2500000000 : ℝ)|=(505249799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375689523/10000000000 : ℝ)|^4189 ≤ (21988176032599/50000000000000 : ℝ)^3165
        have hw : |(5375689523/10000000000 : ℝ)|=(5375689523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343922167/2500000000 : ℝ)|^4189 ≤ (1759053712313/4000000000000 : ℝ)^3165
        have hw : |(1343922167/2500000000 : ℝ)|=(1343922167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296362017/10000000000 : ℝ)*x 0 + (-1064342243/5000000000 : ℝ)*x 1 + (2687844647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296362017/10000000000 : ℝ)^4189 ≤ (43119503626041/100000000000000 : ℝ)^3165 := by
    have hnat : (5296362017 : ℕ)^4189*100000000000000^3165 ≤ 43119503626041^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296362017 10000000000 43119503626041 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064342243/5000000000 : ℝ)^4189 ≤ (12904146762531/100000000000000 : ℝ)^3165 := by
    have hnat : (1064342243 : ℕ)^4189*100000000000000^3165 ≤ 12904146762531^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064342243 5000000000 12904146762531 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687844647/5000000000 : ℝ)^4189 ≤ (21988174792869/50000000000000 : ℝ)^3165 := by
    have hnat : (2687844647 : ℕ)^4189*50000000000000^3165 ≤ 21988174792869^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687844647 5000000000 21988174792869 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296362017/10000000000 : ℝ), (-1064342243/5000000000 : ℝ), (2687844647/5000000000 : ℝ)] ![(43119503626041/100000000000000 : ℝ), (12904146762531/100000000000000 : ℝ), (21988174792869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296362017/10000000000 : ℝ)|^4189 ≤ (43119503626041/100000000000000 : ℝ)^3165
        have hw : |(5296362017/10000000000 : ℝ)|=(5296362017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064342243/5000000000 : ℝ)|^4189 ≤ (12904146762531/100000000000000 : ℝ)^3165
        have hw : |(-1064342243/5000000000 : ℝ)|=(1064342243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687844647/5000000000 : ℝ)|^4189 ≤ (21988174792869/50000000000000 : ℝ)^3165
        have hw : |(2687844647/5000000000 : ℝ)|=(2687844647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296361773/10000000000 : ℝ)*x 0 + (5375689327/10000000000 : ℝ)*x 1 + (-212868477/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296361773/10000000000 : ℝ)^4189 ≤ (2694968812303/6250000000000 : ℝ)^3165 := by
    have hnat : (5296361773 : ℕ)^4189*6250000000000^3165 ≤ 2694968812303^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296361773 10000000000 2694968812303 6250000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375689327/10000000000 : ℝ)^4189 ≤ (34356523393/78125000000 : ℝ)^3165 := by
    have hnat : (5375689327 : ℕ)^4189*78125000000^3165 ≤ 34356523393^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375689327 10000000000 34356523393 78125000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212868477/1000000000 : ℝ)^4189 ≤ (12904149041157/100000000000000 : ℝ)^3165 := by
    have hnat : (212868477 : ℕ)^4189*100000000000000^3165 ≤ 12904149041157^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212868477 1000000000 12904149041157 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296361773/10000000000 : ℝ), (5375689327/10000000000 : ℝ), (-212868477/1000000000 : ℝ)] ![(2694968812303/6250000000000 : ℝ), (34356523393/78125000000 : ℝ), (12904149041157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296361773/10000000000 : ℝ)|^4189 ≤ (2694968812303/6250000000000 : ℝ)^3165
        have hw : |(5296361773/10000000000 : ℝ)|=(5296361773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375689327/10000000000 : ℝ)|^4189 ≤ (34356523393/78125000000 : ℝ)^3165
        have hw : |(5375689327/10000000000 : ℝ)|=(5375689327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212868477/1000000000 : ℝ)|^4189 ≤ (12904149041157/100000000000000 : ℝ)^3165
        have hw : |(-212868477/1000000000 : ℝ)|=(212868477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4465748697/10000000000 : ℝ)*x 0 + (1076795789/2500000000 : ℝ)*x 1 + (4307183623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4465748697/10000000000 : ℝ)^4189 ≤ (8601249345321/25000000000000 : ℝ)^3165 := by
    have hnat : (4465748697 : ℕ)^4189*25000000000000^3165 ≤ 8601249345321^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465748697 10000000000 8601249345321 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076795789/2500000000 : ℝ)^4189 ≤ (3279749895251/10000000000000 : ℝ)^3165 := by
    have hnat : (1076795789 : ℕ)^4189*10000000000000^3165 ≤ 3279749895251^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076795789 2500000000 3279749895251 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4307183623/10000000000 : ℝ)^4189 ≤ (32797503659041/100000000000000 : ℝ)^3165 := by
    have hnat : (4307183623 : ℕ)^4189*100000000000000^3165 ≤ 32797503659041^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307183623 10000000000 32797503659041 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4465748697/10000000000 : ℝ), (1076795789/2500000000 : ℝ), (4307183623/10000000000 : ℝ)] ![(8601249345321/25000000000000 : ℝ), (3279749895251/10000000000000 : ℝ), (32797503659041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4465748697/10000000000 : ℝ)|^4189 ≤ (8601249345321/25000000000000 : ℝ)^3165
        have hw : |(4465748697/10000000000 : ℝ)|=(4465748697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076795789/2500000000 : ℝ)|^4189 ≤ (3279749895251/10000000000000 : ℝ)^3165
        have hw : |(1076795789/2500000000 : ℝ)|=(1076795789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4307183623/10000000000 : ℝ)|^4189 ≤ (32797503659041/100000000000000 : ℝ)^3165
        have hw : |(4307183623/10000000000 : ℝ)|=(4307183623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-454674193/2000000000 : ℝ)*x 0 + (2640832341/5000000000 : ℝ)*x 1 + (660208099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454674193/2000000000 : ℝ)^4189 ≤ (1407758810699/10000000000000 : ℝ)^3165 := by
    have hnat : (454674193 : ℕ)^4189*10000000000000^3165 ≤ 1407758810699^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454674193 2000000000 1407758810699 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640832341/5000000000 : ℝ)^4189 ≤ (21480602671283/50000000000000 : ℝ)^3165 := by
    have hnat : (2640832341 : ℕ)^4189*50000000000000^3165 ≤ 21480602671283^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640832341 5000000000 21480602671283 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660208099/1250000000 : ℝ)^4189 ≤ (42961206526793/100000000000000 : ℝ)^3165 := by
    have hnat : (660208099 : ℕ)^4189*100000000000000^3165 ≤ 42961206526793^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660208099 1250000000 42961206526793 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-454674193/2000000000 : ℝ), (2640832341/5000000000 : ℝ), (660208099/1250000000 : ℝ)] ![(1407758810699/10000000000000 : ℝ), (21480602671283/50000000000000 : ℝ), (42961206526793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-454674193/2000000000 : ℝ)|^4189 ≤ (1407758810699/10000000000000 : ℝ)^3165
        have hw : |(-454674193/2000000000 : ℝ)|=(454674193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640832341/5000000000 : ℝ)|^4189 ≤ (21480602671283/50000000000000 : ℝ)^3165
        have hw : |(2640832341/5000000000 : ℝ)|=(2640832341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660208099/1250000000 : ℝ)|^4189 ≤ (42961206526793/100000000000000 : ℝ)^3165
        have hw : |(660208099/1250000000 : ℝ)|=(660208099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214509063/400000000 : ℝ)*x 0 + (-2165795733/10000000000 : ℝ)*x 1 + (16505203/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214509063/400000000 : ℝ)^4189 ≤ (43836052634639/100000000000000 : ℝ)^3165 := by
    have hnat : (214509063 : ℕ)^4189*100000000000000^3165 ≤ 43836052634639^3165*400000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214509063 400000000 43836052634639 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2165795733/10000000000 : ℝ)^4189 ≤ (105621912087/800000000000 : ℝ)^3165 := by
    have hnat : (2165795733 : ℕ)^4189*800000000000^3165 ≤ 105621912087^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165795733 10000000000 105621912087 800000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16505203/31250000 : ℝ)^4189 ≤ (42961208335431/100000000000000 : ℝ)^3165 := by
    have hnat : (16505203 : ℕ)^4189*100000000000000^3165 ≤ 42961208335431^3165*31250000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16505203 31250000 42961208335431 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214509063/400000000 : ℝ), (-2165795733/10000000000 : ℝ), (16505203/31250000 : ℝ)] ![(43836052634639/100000000000000 : ℝ), (105621912087/800000000000 : ℝ), (42961208335431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214509063/400000000 : ℝ)|^4189 ≤ (43836052634639/100000000000000 : ℝ)^3165
        have hw : |(214509063/400000000 : ℝ)|=(214509063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2165795733/10000000000 : ℝ)|^4189 ≤ (105621912087/800000000000 : ℝ)^3165
        have hw : |(-2165795733/10000000000 : ℝ)|=(2165795733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16505203/31250000 : ℝ)|^4189 ≤ (42961208335431/100000000000000 : ℝ)^3165
        have hw : |(16505203/31250000 : ℝ)|=(16505203/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167585203/312500000 : ℝ)*x 0 + (52816651/100000000 : ℝ)*x 1 + (-2165795653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167585203/312500000 : ℝ)^4189 ≤ (43836051779947/100000000000000 : ℝ)^3165 := by
    have hnat : (167585203 : ℕ)^4189*100000000000000^3165 ≤ 43836051779947^3165*312500000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167585203 312500000 43836051779947 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52816651/100000000 : ℝ)^4189 ≤ (42961209842629/100000000000000 : ℝ)^3165 := by
    have hnat : (52816651 : ℕ)^4189*100000000000000^3165 ≤ 42961209842629^3165*100000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52816651 100000000 42961209842629 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165795653/10000000000 : ℝ)^4189 ≤ (13202738365409/100000000000000 : ℝ)^3165 := by
    have hnat : (2165795653 : ℕ)^4189*100000000000000^3165 ≤ 13202738365409^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165795653 10000000000 13202738365409 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167585203/312500000 : ℝ), (52816651/100000000 : ℝ), (-2165795653/10000000000 : ℝ)] ![(43836051779947/100000000000000 : ℝ), (42961209842629/100000000000000 : ℝ), (13202738365409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167585203/312500000 : ℝ)|^4189 ≤ (43836051779947/100000000000000 : ℝ)^3165
        have hw : |(167585203/312500000 : ℝ)|=(167585203/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52816651/100000000 : ℝ)|^4189 ≤ (42961209842629/100000000000000 : ℝ)^3165
        have hw : |(52816651/100000000 : ℝ)|=(52816651/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2165795653/10000000000 : ℝ)|^4189 ≤ (13202738365409/100000000000000 : ℝ)^3165
        have hw : |(-2165795653/10000000000 : ℝ)|=(2165795653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125588913/5000000000 : ℝ)*x 0 + (551806073/1250000000 : ℝ)*x 1 + (275903003/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125588913/5000000000 : ℝ)^4189 ≤ (32234255417103/100000000000000 : ℝ)^3165 := by
    have hnat : (2125588913 : ℕ)^4189*100000000000000^3165 ≤ 32234255417103^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125588913 5000000000 32234255417103 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551806073/1250000000 : ℝ)^4189 ≤ (33882875007761/100000000000000 : ℝ)^3165 := by
    have hnat : (551806073 : ℕ)^4189*100000000000000^3165 ≤ 33882875007761^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551806073 1250000000 33882875007761 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275903003/625000000 : ℝ)^4189 ≤ (33882869562669/100000000000000 : ℝ)^3165 := by
    have hnat : (275903003 : ℕ)^4189*100000000000000^3165 ≤ 33882869562669^3165*625000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275903003 625000000 33882869562669 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125588913/5000000000 : ℝ), (551806073/1250000000 : ℝ), (275903003/625000000 : ℝ)] ![(32234255417103/100000000000000 : ℝ), (33882875007761/100000000000000 : ℝ), (33882869562669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125588913/5000000000 : ℝ)|^4189 ≤ (32234255417103/100000000000000 : ℝ)^3165
        have hw : |(2125588913/5000000000 : ℝ)|=(2125588913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551806073/1250000000 : ℝ)|^4189 ≤ (33882875007761/100000000000000 : ℝ)^3165
        have hw : |(551806073/1250000000 : ℝ)|=(551806073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275903003/625000000 : ℝ)|^4189 ≤ (33882869562669/100000000000000 : ℝ)^3165
        have hw : |(275903003/625000000 : ℝ)|=(275903003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_8 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220547683/10000000000 : ℝ)*x 0 + (1043527491/2000000000 : ℝ)*x 1 + (1346325169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220547683/10000000000 : ℝ)^4189 ≤ (13646291747143/100000000000000 : ℝ)^3165 := by
    have hnat : (2220547683 : ℕ)^4189*100000000000000^3165 ≤ 13646291747143^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220547683 10000000000 13646291747143 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043527491/2000000000 : ℝ)^4189 ≤ (10568315720917/25000000000000 : ℝ)^3165 := by
    have hnat : (1043527491 : ℕ)^4189*25000000000000^3165 ≤ 10568315720917^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043527491 2000000000 10568315720917 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346325169/2500000000 : ℝ)^4189 ≤ (22040222673443/50000000000000 : ℝ)^3165 := by
    have hnat : (1346325169 : ℕ)^4189*50000000000000^3165 ≤ 22040222673443^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346325169 2500000000 22040222673443 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220547683/10000000000 : ℝ), (1043527491/2000000000 : ℝ), (1346325169/2500000000 : ℝ)] ![(13646291747143/100000000000000 : ℝ), (10568315720917/25000000000000 : ℝ), (22040222673443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220547683/10000000000 : ℝ)|^4189 ≤ (13646291747143/100000000000000 : ℝ)^3165
        have hw : |(-2220547683/10000000000 : ℝ)|=(2220547683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043527491/2000000000 : ℝ)|^4189 ≤ (10568315720917/25000000000000 : ℝ)^3165
        have hw : |(1043527491/2000000000 : ℝ)|=(1043527491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346325169/2500000000 : ℝ)|^4189 ≤ (22040222673443/50000000000000 : ℝ)^3165
        have hw : |(1346325169/2500000000 : ℝ)|=(1346325169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_9 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289575149/10000000000 : ℝ)*x 0 + (-265602777/1250000000 : ℝ)*x 1 + (5385300617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289575149/10000000000 : ℝ)^4189 ≤ (43046387684537/100000000000000 : ℝ)^3165 := by
    have hnat : (5289575149 : ℕ)^4189*100000000000000^3165 ≤ 43046387684537^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289575149 10000000000 43046387684537 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265602777/1250000000 : ℝ)^4189 ≤ (12873167595699/100000000000000 : ℝ)^3165 := by
    have hnat : (265602777 : ℕ)^4189*100000000000000^3165 ≤ 12873167595699^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265602777 1250000000 12873167595699 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385300617/10000000000 : ℝ)^4189 ≤ (5510055588463/12500000000000 : ℝ)^3165 := by
    have hnat : (5385300617 : ℕ)^4189*12500000000000^3165 ≤ 5510055588463^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385300617 10000000000 5510055588463 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289575149/10000000000 : ℝ), (-265602777/1250000000 : ℝ), (5385300617/10000000000 : ℝ)] ![(43046387684537/100000000000000 : ℝ), (12873167595699/100000000000000 : ℝ), (5510055588463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289575149/10000000000 : ℝ)|^4189 ≤ (43046387684537/100000000000000 : ℝ)^3165
        have hw : |(5289575149/10000000000 : ℝ)|=(5289575149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265602777/1250000000 : ℝ)|^4189 ≤ (12873167595699/100000000000000 : ℝ)^3165
        have hw : |(-265602777/1250000000 : ℝ)|=(265602777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385300617/10000000000 : ℝ)|^4189 ≤ (5510055588463/12500000000000 : ℝ)^3165
        have hw : |(5385300617/10000000000 : ℝ)|=(5385300617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_10 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644787577/5000000000 : ℝ)*x 0 + (134632517/250000000 : ℝ)*x 1 + (-531205531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644787577/5000000000 : ℝ)^4189 ≤ (43046387738391/100000000000000 : ℝ)^3165 := by
    have hnat : (2644787577 : ℕ)^4189*100000000000000^3165 ≤ 43046387738391^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644787577 5000000000 43046387738391 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134632517/250000000 : ℝ)^4189 ≤ (44080445390221/100000000000000 : ℝ)^3165 := by
    have hnat : (134632517 : ℕ)^4189*100000000000000^3165 ≤ 44080445390221^3165*250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134632517 250000000 44080445390221 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531205531/2500000000 : ℝ)^4189 ≤ (6436583428993/50000000000000 : ℝ)^3165 := by
    have hnat : (531205531 : ℕ)^4189*50000000000000^3165 ≤ 6436583428993^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531205531 2500000000 6436583428993 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644787577/5000000000 : ℝ), (134632517/250000000 : ℝ), (-531205531/2500000000 : ℝ)] ![(43046387738391/100000000000000 : ℝ), (44080445390221/100000000000000 : ℝ), (6436583428993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644787577/5000000000 : ℝ)|^4189 ≤ (43046387738391/100000000000000 : ℝ)^3165
        have hw : |(2644787577/5000000000 : ℝ)|=(2644787577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134632517/250000000 : ℝ)|^4189 ≤ (44080445390221/100000000000000 : ℝ)^3165
        have hw : |(134632517/250000000 : ℝ)|=(134632517/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531205531/2500000000 : ℝ)|^4189 ≤ (6436583428993/50000000000000 : ℝ)^3165
        have hw : |(-531205531/2500000000 : ℝ)|=(531205531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_11 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (89748187/200000000 : ℝ)*x 0 + (343697/800000 : ℝ)*x 1 + (2148106277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89748187/200000000 : ℝ)^4189 ≤ (8656509959909/25000000000000 : ℝ)^3165 := by
    have hnat : (89748187 : ℕ)^4189*25000000000000^3165 ≤ 8656509959909^3165*200000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89748187 200000000 8656509959909 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343697/800000 : ℝ)^4189 ≤ (32686979800117/100000000000000 : ℝ)^3165 := by
    have hnat : (343697 : ℕ)^4189*100000000000000^3165 ≤ 32686979800117^3165*800000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343697 800000 32686979800117 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148106277/5000000000 : ℝ)^4189 ≤ (8171745085973/25000000000000 : ℝ)^3165 := by
    have hnat : (2148106277 : ℕ)^4189*25000000000000^3165 ≤ 8171745085973^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148106277 5000000000 8171745085973 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89748187/200000000 : ℝ), (343697/800000 : ℝ), (2148106277/5000000000 : ℝ)] ![(8656509959909/25000000000000 : ℝ), (32686979800117/100000000000000 : ℝ), (8171745085973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89748187/200000000 : ℝ)|^4189 ≤ (8656509959909/25000000000000 : ℝ)^3165
        have hw : |(89748187/200000000 : ℝ)|=(89748187/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343697/800000 : ℝ)|^4189 ≤ (32686979800117/100000000000000 : ℝ)^3165
        have hw : |(343697/800000 : ℝ)|=(343697/800000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2148106277/5000000000 : ℝ)|^4189 ≤ (8171745085973/25000000000000 : ℝ)^3165
        have hw : |(2148106277/5000000000 : ℝ)|=(2148106277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_12 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074114989/10000000000 : ℝ)*x 0 + (5438469111/10000000000 : ℝ)*x 1 + (1318401917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074114989/10000000000 : ℝ)^4189 ≤ (12468143981149/100000000000000 : ℝ)^3165 := by
    have hnat : (2074114989 : ℕ)^4189*100000000000000^3165 ≤ 12468143981149^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074114989 10000000000 12468143981149 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438469111/10000000000 : ℝ)^4189 ≤ (22328684321769/50000000000000 : ℝ)^3165 := by
    have hnat : (5438469111 : ℕ)^4189*50000000000000^3165 ≤ 22328684321769^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438469111 10000000000 22328684321769 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318401917/2500000000 : ℝ)^4189 ≤ (21437243679217/50000000000000 : ℝ)^3165 := by
    have hnat : (1318401917 : ℕ)^4189*50000000000000^3165 ≤ 21437243679217^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318401917 2500000000 21437243679217 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074114989/10000000000 : ℝ), (5438469111/10000000000 : ℝ), (1318401917/2500000000 : ℝ)] ![(12468143981149/100000000000000 : ℝ), (22328684321769/50000000000000 : ℝ), (21437243679217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074114989/10000000000 : ℝ)|^4189 ≤ (12468143981149/100000000000000 : ℝ)^3165
        have hw : |(-2074114989/10000000000 : ℝ)|=(2074114989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438469111/10000000000 : ℝ)|^4189 ≤ (22328684321769/50000000000000 : ℝ)^3165
        have hw : |(5438469111/10000000000 : ℝ)|=(5438469111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318401917/2500000000 : ℝ)|^4189 ≤ (21437243679217/50000000000000 : ℝ)^3165
        have hw : |(1318401917/2500000000 : ℝ)|=(1318401917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_13 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368412259/10000000000 : ℝ)*x 0 + (-1084458897/5000000000 : ℝ)*x 1 + (1054721571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368412259/10000000000 : ℝ)^4189 ≤ (21948787966617/50000000000000 : ℝ)^3165 := by
    have hnat : (5368412259 : ℕ)^4189*50000000000000^3165 ≤ 21948787966617^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368412259 10000000000 21948787966617 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084458897/5000000000 : ℝ)^4189 ≤ (13227934674729/100000000000000 : ℝ)^3165 := by
    have hnat : (1084458897 : ℕ)^4189*100000000000000^3165 ≤ 13227934674729^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084458897 5000000000 13227934674729 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054721571/2000000000 : ℝ)^4189 ≤ (21437244685313/50000000000000 : ℝ)^3165 := by
    have hnat : (1054721571 : ℕ)^4189*50000000000000^3165 ≤ 21437244685313^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054721571 2000000000 21437244685313 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368412259/10000000000 : ℝ), (-1084458897/5000000000 : ℝ), (1054721571/2000000000 : ℝ)] ![(21948787966617/50000000000000 : ℝ), (13227934674729/100000000000000 : ℝ), (21437244685313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368412259/10000000000 : ℝ)|^4189 ≤ (21948787966617/50000000000000 : ℝ)^3165
        have hw : |(5368412259/10000000000 : ℝ)|=(5368412259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084458897/5000000000 : ℝ)|^4189 ≤ (13227934674729/100000000000000 : ℝ)^3165
        have hw : |(-1084458897/5000000000 : ℝ)|=(1084458897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054721571/2000000000 : ℝ)|^4189 ≤ (21437244685313/50000000000000 : ℝ)^3165
        have hw : |(1054721571/2000000000 : ℝ)|=(1054721571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_14 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368412899/10000000000 : ℝ)*x 0 + (5273606289/10000000000 : ℝ)*x 1 + (-135557439/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368412899/10000000000 : ℝ)^4189 ≤ (43897582859693/100000000000000 : ℝ)^3165 := by
    have hnat : (5368412899 : ℕ)^4189*100000000000000^3165 ≤ 43897582859693^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368412899 10000000000 43897582859693 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273606289/10000000000 : ℝ)^4189 ≤ (21437236259933/50000000000000 : ℝ)^3165 := by
    have hnat : (5273606289 : ℕ)^4189*50000000000000^3165 ≤ 21437236259933^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273606289 10000000000 21437236259933 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135557439/625000000 : ℝ)^4189 ≤ (51671658607/390625000000 : ℝ)^3165 := by
    have hnat : (135557439 : ℕ)^4189*390625000000^3165 ≤ 51671658607^3165*625000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135557439 625000000 51671658607 390625000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368412899/10000000000 : ℝ), (5273606289/10000000000 : ℝ), (-135557439/625000000 : ℝ)] ![(43897582859693/100000000000000 : ℝ), (21437236259933/50000000000000 : ℝ), (51671658607/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368412899/10000000000 : ℝ)|^4189 ≤ (43897582859693/100000000000000 : ℝ)^3165
        have hw : |(5368412899/10000000000 : ℝ)|=(5368412899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273606289/10000000000 : ℝ)|^4189 ≤ (21437236259933/50000000000000 : ℝ)^3165
        have hw : |(5273606289/10000000000 : ℝ)|=(5273606289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135557439/625000000 : ℝ)|^4189 ≤ (51671658607/390625000000 : ℝ)^3165
        have hw : |(-135557439/625000000 : ℝ)|=(135557439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_box_15 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4232559027/10000000000 : ℝ)*x 0 + (176945427/400000000 : ℝ)*x 1 + (884726977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4232559027/10000000000 : ℝ)^4189 ≤ (8011884098117/25000000000000 : ℝ)^3165 := by
    have hnat : (4232559027 : ℕ)^4189*25000000000000^3165 ≤ 8011884098117^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232559027 10000000000 8011884098117 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176945427/400000000 : ℝ)^4189 ≤ (16988117904857/50000000000000 : ℝ)^3165 := by
    have hnat : (176945427 : ℕ)^4189*50000000000000^3165 ≤ 16988117904857^3165*400000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176945427 400000000 16988117904857 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884726977/2000000000 : ℝ)^4189 ≤ (33976227778899/100000000000000 : ℝ)^3165 := by
    have hnat : (884726977 : ℕ)^4189*100000000000000^3165 ≤ 33976227778899^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884726977 2000000000 33976227778899 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4232559027/10000000000 : ℝ), (176945427/400000000 : ℝ), (884726977/2000000000 : ℝ)] ![(8011884098117/25000000000000 : ℝ), (16988117904857/50000000000000 : ℝ), (33976227778899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4232559027/10000000000 : ℝ)|^4189 ≤ (8011884098117/25000000000000 : ℝ)^3165
        have hw : |(4232559027/10000000000 : ℝ)|=(4232559027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176945427/400000000 : ℝ)|^4189 ≤ (16988117904857/50000000000000 : ℝ)^3165
        have hw : |(176945427/400000000 : ℝ)|=(176945427/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884726977/2000000000 : ℝ)|^4189 ≤ (33976227778899/100000000000000 : ℝ)^3165
        have hw : |(884726977/2000000000 : ℝ)|=(884726977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62237/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14833/25000 : ℝ) ∧ (79939/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4161/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11409/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (13926102246437671/100000000000000000000 : ℝ) := by
    have hpowers : (11409/100000 : ℝ)^8377 ≤ (13926102246437671/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11409 : ℕ)^8377*100000000000000000000^2048 ≤ 13926102246437671^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11409 100000 13926102246437671 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11409/100000 : ℝ)) (X := (13926102246437671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (6571262043605263/20000000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^8377 ≤ (6571262043605263/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14073 : ℕ)^8377*20000000000000000000^2048 ≤ 6571262043605263^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 6571262043605263 20000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (6571262043605263/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013926102246437671/50000000000000000000 : ℝ) ≤ (625042553505281/625000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50013926102246437671/50000000000000000000 : ℝ)^2048 ≤ (625042553505281/625000000000000 : ℝ)^8377 := by
      have hnat : (50013926102246437671 : ℕ)^2048*625000000000000^8377 ≤ 625042553505281^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013926102246437671 50000000000000000000 625042553505281 625000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625042553505281/625000000000000 : ℝ)) (X := (50013926102246437671/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023391206232231993/50000000000000000000 : ℝ) ≤ (5000571764672463/5000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50023391206232231993/50000000000000000000 : ℝ)^2048 ≤ (5000571764672463/5000000000000000 : ℝ)^8377 := by
      have hnat : (50023391206232231993 : ℕ)^2048*5000000000000000^8377 ≤ 5000571764672463^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023391206232231993 50000000000000000000 5000571764672463 5000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000571764672463/5000000000000000 : ℝ)) (X := (50023391206232231993/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006571262043605263/10000000000000000000 : ℝ) ≤ (2500401550651339/2500000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (10006571262043605263/10000000000000000000 : ℝ)^2048 ≤ (2500401550651339/2500000000000000 : ℝ)^8377 := by
      have hnat : (10006571262043605263 : ℕ)^2048*2500000000000000^8377 ≤ 2500401550651339^8377*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006571262043605263 10000000000000000000 2500401550651339 2500000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500401550651339/2500000000000000 : ℝ)) (X := (10006571262043605263/10000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13926102246437671/100000000000000000000 : ℝ) ≤ ((2219271376846050467/2220000000000000000 : ℝ)+2*(46267326043/26640000000000 : ℝ)*(11409/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (2219271376846050467/2220000000000000000 : ℝ)+2*(46267326043/26640000000000 : ℝ)*(11409/100000 : ℝ)=(625042553505281/625000000000000 : ℝ) by norm_num, show 1+2*(13926102246437671/100000000000000000000 : ℝ)=(50013926102246437671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6571262043605263/20000000000000000000 : ℝ)+(13926102246437671/100000000000000000000 : ℝ) ≤ ((2219271376846050467/2220000000000000000 : ℝ)+(46267326043/26640000000000 : ℝ)*((14073/100000 : ℝ)+(11409/100000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (2219271376846050467/2220000000000000000 : ℝ)+(46267326043/26640000000000 : ℝ)*((14073/100000 : ℝ)+(11409/100000 : ℝ))=(5000571764672463/5000000000000000 : ℝ) by norm_num, show 1+(6571262043605263/20000000000000000000 : ℝ)+(13926102246437671/100000000000000000000 : ℝ)=(50023391206232231993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6571262043605263/20000000000000000000 : ℝ) ≤ ((2219271376846050467/2220000000000000000 : ℝ)+2*(46267326043/26640000000000 : ℝ)*(14073/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (2219271376846050467/2220000000000000000 : ℝ)+2*(46267326043/26640000000000 : ℝ)*(14073/100000 : ℝ)=(2500401550651339/2500000000000000 : ℝ) by norm_num, show 1+2*(6571262043605263/20000000000000000000 : ℝ)=(10006571262043605263/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2219271376846050467/2220000000000000000 : ℝ)*(X 1 0+X 2 0)+(46267326043/26640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (2219271376846050467/2220000000000000000 : ℝ)) (alpha := (46267326043/26640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2219271376846050467/2220000000000000000 : ℝ)*(X 0 1+X 2 1)+(46267326043/26640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (2219271376846050467/2220000000000000000 : ℝ)) (alpha := (46267326043/26640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2219271376846050467/2220000000000000000 : ℝ)*(X 0 2+X 1 2)+(46267326043/26640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (2219271376846050467/2220000000000000000 : ℝ)) (alpha := (46267326043/26640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-505249799/2500000000 : ℝ)*X 0 0+(5375689523/10000000000 : ℝ)*X 0 1+(1343922167/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296362017/10000000000 : ℝ)*X 1 0+(-1064342243/5000000000 : ℝ)*X 1 1+(2687844647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296361773/10000000000 : ℝ)*X 2 0+(5375689327/10000000000 : ℝ)*X 2 1+(-212868477/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4465748697/10000000000 : ℝ)*X 0 0+(1076795789/2500000000 : ℝ)*X 0 1+(4307183623/10000000000 : ℝ)*X 0 2+(4465748697/10000000000 : ℝ)*X 1 0+(1076795789/2500000000 : ℝ)*X 1 1+(4307183623/10000000000 : ℝ)*X 1 2+(4465748697/10000000000 : ℝ)*X 2 0+(1076795789/2500000000 : ℝ)*X 2 1+(4307183623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-454674193/2000000000 : ℝ)*X 0 0+(2640832341/5000000000 : ℝ)*X 0 1+(660208099/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((214509063/400000000 : ℝ)*X 1 0+(-2165795733/10000000000 : ℝ)*X 1 1+(16505203/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((167585203/312500000 : ℝ)*X 2 0+(52816651/100000000 : ℝ)*X 2 1+(-2165795653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2125588913/5000000000 : ℝ)*X 0 0+(551806073/1250000000 : ℝ)*X 0 1+(275903003/625000000 : ℝ)*X 0 2+(2125588913/5000000000 : ℝ)*X 1 0+(551806073/1250000000 : ℝ)*X 1 1+(275903003/625000000 : ℝ)*X 1 2+(2125588913/5000000000 : ℝ)*X 2 0+(551806073/1250000000 : ℝ)*X 2 1+(275903003/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2220547683/10000000000 : ℝ)*X 0 0+(1043527491/2000000000 : ℝ)*X 0 1+(1346325169/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289575149/10000000000 : ℝ)*X 1 0+(-265602777/1250000000 : ℝ)*X 1 1+(5385300617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644787577/5000000000 : ℝ)*X 2 0+(134632517/250000000 : ℝ)*X 2 1+(-531205531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((89748187/200000000 : ℝ)*X 0 0+(343697/800000 : ℝ)*X 0 1+(2148106277/5000000000 : ℝ)*X 0 2+(89748187/200000000 : ℝ)*X 1 0+(343697/800000 : ℝ)*X 1 1+(2148106277/5000000000 : ℝ)*X 1 2+(89748187/200000000 : ℝ)*X 2 0+(343697/800000 : ℝ)*X 2 1+(2148106277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2074114989/10000000000 : ℝ)*X 0 0+(5438469111/10000000000 : ℝ)*X 0 1+(1318401917/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368412259/10000000000 : ℝ)*X 1 0+(-1084458897/5000000000 : ℝ)*X 1 1+(1054721571/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368412899/10000000000 : ℝ)*X 2 0+(5273606289/10000000000 : ℝ)*X 2 1+(-135557439/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4232559027/10000000000 : ℝ)*X 0 0+(176945427/400000000 : ℝ)*X 0 1+(884726977/2000000000 : ℝ)*X 0 2+(4232559027/10000000000 : ℝ)*X 1 0+(176945427/400000000 : ℝ)*X 1 1+(884726977/2000000000 : ℝ)*X 1 2+(4232559027/10000000000 : ℝ)*X 2 0+(176945427/400000000 : ℝ)*X 2 1+(884726977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62237/100000 : ℝ) ≤ (-3684273296321641031924799/5920000000000000000000000 : ℝ) := by norm_num
    linear_combination (27498461/25000000000000 : ℝ)*(lower0) + (24608867/20000000000000 : ℝ)*(lower2) + (45191869/50000000000000 : ℝ)*(lower4) + (29619229/100000000000000 : ℝ)*(lower5) + (3956203636073847/100000000000000 : ℝ)*(major0) + (3956203636073847/100000000000000 : ℝ)*(major1) + (3956203636073847/100000000000000 : ℝ)*(major2) + (82830913840479/1562500000000 : ℝ)*(sp4) + (331319510943059/6250000000000 : ℝ)*(sp5) + (662622637421279/12500000000000 : ℝ)*(sp6) + (1315985189100879/50000000000000 : ℝ)*(sp7) + (3190229151/100000000000000 : ℝ)*(sp8) + (69500930863/100000000000000 : ℝ)*(sp13) + (25072081197/12500000000000 : ℝ)*(sp14) + (1315985189100879/50000000000000 : ℝ)*(f.failure) + (5301181676019807/100000000000000 : ℝ)*(f.sum) + (1032463080889/148000000000000000000000000 : ℝ)*base65 + (2006303468780059/2000000000000000000000000000000 : ℝ)*base67 + (3697532982780059/2000000000000000000000000000000 : ℝ)*base69 + (18007540156780059/2000000000000000000000000000000 : ℝ)*base71 + (14952400487/29600000000000000000000000 : ℝ)*base74 + (7870349971219941/2000000000000000000000000000000 : ℝ)*base76 + (10478883001219941/2000000000000000000000000000000 : ℝ)*base78 + (21883345665219941/2000000000000000000000000000000 : ℝ)*base80 + (761752561797/148000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3326949/250000000000000000000 : ℝ)*base90 + (3326949/250000000000000000000 : ℝ)*base92 + (3326949/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14833/25000 : ℝ) ≤ (10976872622305244308467956123737/18500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45405813/20000000000000 : ℝ)*(upper0) + (40882399/25000000000000 : ℝ)*(upper2) + (174203987/50000000000000 : ℝ)*(upper3) + (8150733/10000000000000 : ℝ)*(upper4) + (16814279/25000000000000 : ℝ)*(upper5) + (2010533356585811/50000000000000 : ℝ)*(major0) + (2010533356585811/50000000000000 : ℝ)*(major1) + (2010533356585811/50000000000000 : ℝ)*(major2) + (5347233000820189/100000000000000 : ℝ)*(sp0) + (5347218776776101/100000000000000 : ℝ)*(sp1) + (5347227154860657/100000000000000 : ℝ)*(sp2) + (2675122276654029/100000000000000 : ℝ)*(sp3) + (1461489883/25000000000000 : ℝ)*(sp6) + (1778005511/12500000000000 : ℝ)*(sp9) + (2675122276654029/100000000000000 : ℝ)*(f.failure) + (5347233000820189/100000000000000 : ℝ)*(f.sum) + (350334451319/666000000000000000000000000 : ℝ)*base65 + (3281617356530303/9000000000000000000000000000000 : ℝ)*base67 + (40830712175469697/9000000000000000000000000000000 : ℝ)*base70 + (47707519682469697/9000000000000000000000000000000 : ℝ)*base72 + (27861978427493/666000000000000000000000000 : ℝ)*base73 + (46315732817469697/9000000000000000000000000000000 : ℝ)*base76 + (69862818818469697/9000000000000000000000000000000 : ℝ)*base78 + (41354666628530303/9000000000000000000000000000000 : ℝ)*base79 + (103329172273/666000000000000000000000000 : ℝ)*base82 + (519599/500000000000000000000 : ℝ)*base90 + (519599/500000000000000000000 : ℝ)*base92 + (519599/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79939/100000 : ℝ) ≤ (88734835248220182161280217/111000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8607671/100000000000000 : ℝ)*(lower1) + (46427333/100000000000000 : ℝ)*(lower3) + (3878609/12500000000000 : ℝ)*(upper4) + (561070140529699/12500000000000 : ℝ)*(major0) + (561070140529699/12500000000000 : ℝ)*(major1) + (561070140529699/12500000000000 : ℝ)*(major2) + (35513909/100000000000000 : ℝ)*(sp0) + (17324497/625000000000 : ℝ)*(sp1) + (4409849259/10000000000000 : ℝ)*(sp2) + (12506395653/50000000000000 : ℝ)*(sp3) + (5964339666643357/100000000000000 : ℝ)*(sp8) + (1192867386047549/20000000000000 : ℝ)*(sp9) + (238571824146587/4000000000000 : ℝ)*(sp10) + (746527608963611/25000000000000 : ℝ)*(sp11) + (11944541794583/400000000000 : ℝ)*(f.failure) + (1192867940431453/20000000000000 : ℝ)*(f.sum) + (777795736657/333000000000000000000000000 : ℝ)*base66 + (15634330154197073/2250000000000000000000000000000 : ℝ)*base68 + (209696733540802927/2250000000000000000000000000000 : ℝ)*base69 + (6613789210552927/2250000000000000000000000000000 : ℝ)*base71 + (143916882073/166500000000000000000000000 : ℝ)*base73 + (56541525211447073/2250000000000000000000000000000 : ℝ)*base76 + (19428492816802927/2250000000000000000000000000000 : ℝ)*base77 + (5461751852197073/2250000000000000000000000000000 : ℝ)*base80 + (9004361636663/83250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (18973/2000000000000000000 : ℝ)*base90 + (18973/2000000000000000000 : ℝ)*base92 + (18973/2000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-4161/5000 : ℝ) ≤ (-46185905941363975316210249020231/55500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67295037/6250000000000 : ℝ)*(lower0) + (291339119/50000000000000 : ℝ)*(lower1) + (251690381/50000000000000 : ℝ)*(lower4) + (4523755491568169/100000000000000 : ℝ)*(major0) + (4523755491568169/100000000000000 : ℝ)*(major1) + (4523755491568169/100000000000000 : ℝ)*(major2) + (2418481757/20000000000000 : ℝ)*(sp0) + (147122359867/20000000000000 : ℝ)*(sp5) + (2303444264859/100000000000000 : ℝ)*(sp6) + (182996210221/100000000000000 : ℝ)*(sp7) + (6065688729894157/100000000000000 : ℝ)*(sp12) + (6064965210503607/100000000000000 : ℝ)*(sp13) + (6063397378038083/100000000000000 : ℝ)*(sp14) + (150468322373541/5000000000000 : ℝ)*(sp15) + (3009549443681041/100000000000000 : ℝ)*(f.failure) + (3032850411151471/50000000000000 : ℝ)*(f.sum) + (7311361848671/1332000000000000000000000000 : ℝ)*base65 + (155915552499591763/18000000000000000000000000000000 : ℝ)*base68 + (244572284823591763/18000000000000000000000000000000 : ℝ)*base70 + (284190266103591763/18000000000000000000000000000000 : ℝ)*base72 + (15112537907467/266400000000000000000000000 : ℝ)*base73 + (227833910745591763/18000000000000000000000000000000 : ℝ)*base76 + (391057901277591763/18000000000000000000000000000000 : ℝ)*base78 + (1330425791210408237/18000000000000000000000000000000 : ℝ)*base79 + (664269147119/1332000000000000000000000000 : ℝ)*base81 + (731429/500000000000000000000 : ℝ)*base89 + (731429/500000000000000000000 : ℝ)*base91 + (731429/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1185_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14833/25000 : ℝ) else (79939/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4161/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1185_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1185_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14833/25000 : ℝ) else (79939/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4161/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1185_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14833/25000 : ℝ) else (79939/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4161/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
