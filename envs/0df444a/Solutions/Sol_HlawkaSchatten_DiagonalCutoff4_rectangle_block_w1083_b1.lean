-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1083_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:51:21.765669+00:00
-- url     : https://prove2.me/submissions/75a42e8f-a63e-4eb6-b1b3-85dd71cfbc9b

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
theorem support_rectangle_w1083_s3_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190913079/10000000000 : ℝ)*x 0 + (5435565543/10000000000 : ℝ)*x 1 + (653275711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190913079/10000000000 : ℝ)^2069 ≤ (13298356300801/100000000000000 : ℝ)^1557 := by
    have hnat : (2190913079 : ℕ)^2069*100000000000000^1557 ≤ 13298356300801^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190913079 10000000000 13298356300801 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435565543/10000000000 : ℝ)^2069 ≤ (22240947261773/50000000000000 : ℝ)^1557 := by
    have hnat : (5435565543 : ℕ)^2069*50000000000000^1557 ≤ 22240947261773^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435565543 10000000000 22240947261773 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653275711/1250000000 : ℝ)^2069 ≤ (10554937288307/25000000000000 : ℝ)^1557 := by
    have hnat : (653275711 : ℕ)^2069*25000000000000^1557 ≤ 10554937288307^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653275711 1250000000 10554937288307 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190913079/10000000000 : ℝ), (5435565543/10000000000 : ℝ), (653275711/1250000000 : ℝ)] ![(13298356300801/100000000000000 : ℝ), (22240947261773/50000000000000 : ℝ), (10554937288307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190913079/10000000000 : ℝ)|^2069 ≤ (13298356300801/100000000000000 : ℝ)^1557
        have hw : |(-2190913079/10000000000 : ℝ)|=(2190913079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435565543/10000000000 : ℝ)|^2069 ≤ (22240947261773/50000000000000 : ℝ)^1557
        have hw : |(5435565543/10000000000 : ℝ)|=(5435565543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653275711/1250000000 : ℝ)|^2069 ≤ (10554937288307/25000000000000 : ℝ)^1557
        have hw : |(653275711/1250000000 : ℝ)|=(653275711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s3_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5355253031/10000000000 : ℝ)*x 0 + (-1149038383/5000000000 : ℝ)*x 1 + (5226205667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355253031/10000000000 : ℝ)^2069 ≤ (436106626149/1000000000000 : ℝ)^1557 := by
    have hnat : (5355253031 : ℕ)^2069*1000000000000^1557 ≤ 436106626149^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355253031 10000000000 436106626149 1000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1149038383/5000000000 : ℝ)^2069 ≤ (14169588436803/100000000000000 : ℝ)^1557 := by
    have hnat : (1149038383 : ℕ)^2069*100000000000000^1557 ≤ 14169588436803^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149038383 5000000000 14169588436803 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226205667/10000000000 : ℝ)^2069 ≤ (21109874463897/50000000000000 : ℝ)^1557 := by
    have hnat : (5226205667 : ℕ)^2069*50000000000000^1557 ≤ 21109874463897^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226205667 10000000000 21109874463897 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355253031/10000000000 : ℝ), (-1149038383/5000000000 : ℝ), (5226205667/10000000000 : ℝ)] ![(436106626149/1000000000000 : ℝ), (14169588436803/100000000000000 : ℝ), (21109874463897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355253031/10000000000 : ℝ)|^2069 ≤ (436106626149/1000000000000 : ℝ)^1557
        have hw : |(5355253031/10000000000 : ℝ)|=(5355253031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1149038383/5000000000 : ℝ)|^2069 ≤ (14169588436803/100000000000000 : ℝ)^1557
        have hw : |(-1149038383/5000000000 : ℝ)|=(1149038383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226205667/10000000000 : ℝ)|^2069 ≤ (21109874463897/50000000000000 : ℝ)^1557
        have hw : |(5226205667/10000000000 : ℝ)|=(5226205667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s3_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1071050591/2000000000 : ℝ)*x 0 + (1045241217/2000000000 : ℝ)*x 1 + (-2298076319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071050591/2000000000 : ℝ)^2069 ≤ (5451332724059/12500000000000 : ℝ)^1557 := by
    have hnat : (1071050591 : ℕ)^2069*12500000000000^1557 ≤ 5451332724059^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071050591 2000000000 5451332724059 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045241217/2000000000 : ℝ)^2069 ≤ (42219753415013/100000000000000 : ℝ)^1557 := by
    have hnat : (1045241217 : ℕ)^2069*100000000000000^1557 ≤ 42219753415013^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045241217 2000000000 42219753415013 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2298076319/10000000000 : ℝ)^2069 ≤ (14169584774349/100000000000000 : ℝ)^1557 := by
    have hnat : (2298076319 : ℕ)^2069*100000000000000^1557 ≤ 14169584774349^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298076319 10000000000 14169584774349 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071050591/2000000000 : ℝ), (1045241217/2000000000 : ℝ), (-2298076319/10000000000 : ℝ)] ![(5451332724059/12500000000000 : ℝ), (42219753415013/100000000000000 : ℝ), (14169584774349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071050591/2000000000 : ℝ)|^2069 ≤ (5451332724059/12500000000000 : ℝ)^1557
        have hw : |(1071050591/2000000000 : ℝ)|=(1071050591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045241217/2000000000 : ℝ)|^2069 ≤ (42219753415013/100000000000000 : ℝ)^1557
        have hw : |(1045241217/2000000000 : ℝ)|=(1045241217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2298076319/10000000000 : ℝ)|^2069 ≤ (14169584774349/100000000000000 : ℝ)^1557
        have hw : |(-2298076319/10000000000 : ℝ)|=(2298076319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s3_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4370383109/10000000000 : ℝ)*x 0 + (833883357/2000000000 : ℝ)*x 1 + (572639633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370383109/10000000000 : ℝ)^2069 ≤ (16644810093791/50000000000000 : ℝ)^1557 := by
    have hnat : (4370383109 : ℕ)^2069*50000000000000^1557 ≤ 16644810093791^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370383109 10000000000 16644810093791 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833883357/2000000000 : ℝ)^2069 ≤ (1954437737211/6250000000000 : ℝ)^1557 := by
    have hnat : (833883357 : ℕ)^2069*6250000000000^1557 ≤ 1954437737211^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833883357 2000000000 1954437737211 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572639633/1250000000 : ℝ)^2069 ≤ (2214960999561/6250000000000 : ℝ)^1557 := by
    have hnat : (572639633 : ℕ)^2069*6250000000000^1557 ≤ 2214960999561^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572639633 1250000000 2214960999561 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370383109/10000000000 : ℝ), (833883357/2000000000 : ℝ), (572639633/1250000000 : ℝ)] ![(16644810093791/50000000000000 : ℝ), (1954437737211/6250000000000 : ℝ), (2214960999561/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370383109/10000000000 : ℝ)|^2069 ≤ (16644810093791/50000000000000 : ℝ)^1557
        have hw : |(4370383109/10000000000 : ℝ)|=(4370383109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833883357/2000000000 : ℝ)|^2069 ≤ (1954437737211/6250000000000 : ℝ)^1557
        have hw : |(833883357/2000000000 : ℝ)|=(833883357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572639633/1250000000 : ℝ)|^2069 ≤ (2214960999561/6250000000000 : ℝ)^1557
        have hw : |(572639633/1250000000 : ℝ)|=(572639633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s3_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-547733619/2500000000 : ℝ)*x 0 + (5227053271/10000000000 : ℝ)*x 1 + (5434712923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547733619/2500000000 : ℝ)^2069 ≤ (6649264441953/50000000000000 : ℝ)^1557 := by
    have hnat : (547733619 : ℕ)^2069*50000000000000^1557 ≤ 6649264441953^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547733619 2500000000 6649264441953 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227053271/10000000000 : ℝ)^2069 ≤ (4222884817797/10000000000000 : ℝ)^1557 := by
    have hnat : (5227053271 : ℕ)^2069*10000000000000^1557 ≤ 4222884817797^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227053271 10000000000 4222884817797 10000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434712923/10000000000 : ℝ)^2069 ≤ (4447262292259/10000000000000 : ℝ)^1557 := by
    have hnat : (5434712923 : ℕ)^2069*10000000000000^1557 ≤ 4447262292259^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434712923 10000000000 4447262292259 10000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547733619/2500000000 : ℝ), (5227053271/10000000000 : ℝ), (5434712923/10000000000 : ℝ)] ![(6649264441953/50000000000000 : ℝ), (4222884817797/10000000000000 : ℝ), (4447262292259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547733619/2500000000 : ℝ)|^2069 ≤ (6649264441953/50000000000000 : ℝ)^1557
        have hw : |(-547733619/2500000000 : ℝ)|=(547733619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227053271/10000000000 : ℝ)|^2069 ≤ (4222884817797/10000000000000 : ℝ)^1557
        have hw : |(5227053271/10000000000 : ℝ)|=(5227053271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434712923/10000000000 : ℝ)|^2069 ≤ (4447262292259/10000000000000 : ℝ)^1557
        have hw : |(5434712923/10000000000 : ℝ)|=(5434712923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s3_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302446413/10000000000 : ℝ)*x 0 + (-417913871/2000000000 : ℝ)*x 1 + (217388529/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302446413/10000000000 : ℝ)^2069 ≤ (43040148133831/100000000000000 : ℝ)^1557 := by
    have hnat : (5302446413 : ℕ)^2069*100000000000000^1557 ≤ 43040148133831^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302446413 10000000000 43040148133831 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417913871/2000000000 : ℝ)^2069 ≤ (12487225652107/100000000000000 : ℝ)^1557 := by
    have hnat : (417913871 : ℕ)^2069*100000000000000^1557 ≤ 12487225652107^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417913871 2000000000 12487225652107 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217388529/400000000 : ℝ)^2069 ≤ (694884784477/1562500000000 : ℝ)^1557 := by
    have hnat : (217388529 : ℕ)^2069*1562500000000^1557 ≤ 694884784477^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217388529 400000000 694884784477 1562500000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302446413/10000000000 : ℝ), (-417913871/2000000000 : ℝ), (217388529/400000000 : ℝ)] ![(43040148133831/100000000000000 : ℝ), (12487225652107/100000000000000 : ℝ), (694884784477/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302446413/10000000000 : ℝ)|^2069 ≤ (43040148133831/100000000000000 : ℝ)^1557
        have hw : |(5302446413/10000000000 : ℝ)|=(5302446413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417913871/2000000000 : ℝ)|^2069 ≤ (12487225652107/100000000000000 : ℝ)^1557
        have hw : |(-417913871/2000000000 : ℝ)|=(417913871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217388529/400000000 : ℝ)|^2069 ≤ (694884784477/1562500000000 : ℝ)^1557
        have hw : |(217388529/400000000 : ℝ)|=(217388529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s3_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662805823/1250000000 : ℝ)*x 0 + (1086942591/2000000000 : ℝ)*x 1 + (-522392373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662805823/1250000000 : ℝ)^2069 ≤ (1721605999131/4000000000000 : ℝ)^1557 := by
    have hnat : (662805823 : ℕ)^2069*4000000000000^1557 ≤ 1721605999131^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662805823 1250000000 1721605999131 4000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086942591/2000000000 : ℝ)^2069 ≤ (44472623270557/100000000000000 : ℝ)^1557 := by
    have hnat : (1086942591 : ℕ)^2069*100000000000000^1557 ≤ 44472623270557^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086942591 2000000000 44472623270557 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522392373/2500000000 : ℝ)^2069 ≤ (6243613370019/50000000000000 : ℝ)^1557 := by
    have hnat : (522392373 : ℕ)^2069*50000000000000^1557 ≤ 6243613370019^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522392373 2500000000 6243613370019 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662805823/1250000000 : ℝ), (1086942591/2000000000 : ℝ), (-522392373/2500000000 : ℝ)] ![(1721605999131/4000000000000 : ℝ), (44472623270557/100000000000000 : ℝ), (6243613370019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662805823/1250000000 : ℝ)|^2069 ≤ (1721605999131/4000000000000 : ℝ)^1557
        have hw : |(662805823/1250000000 : ℝ)|=(662805823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086942591/2000000000 : ℝ)|^2069 ≤ (44472623270557/100000000000000 : ℝ)^1557
        have hw : |(1086942591/2000000000 : ℝ)|=(1086942591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522392373/2500000000 : ℝ)|^2069 ≤ (6243613370019/50000000000000 : ℝ)^1557
        have hw : |(-522392373/2500000000 : ℝ)|=(522392373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s3_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4370424699/10000000000 : ℝ)*x 0 + (457945131/1000000000 : ℝ)*x 1 + (1042773119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370424699/10000000000 : ℝ)^2069 ≤ (16645020578627/50000000000000 : ℝ)^1557 := by
    have hnat : (4370424699 : ℕ)^2069*50000000000000^1557 ≤ 16645020578627^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370424699 10000000000 16645020578627 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457945131/1000000000 : ℝ)^2069 ≤ (4427781665541/12500000000000 : ℝ)^1557 := by
    have hnat : (457945131 : ℕ)^2069*12500000000000^1557 ≤ 4427781665541^1557*1000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457945131 1000000000 4427781665541 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042773119/2500000000 : ℝ)^2069 ≤ (31287705508573/100000000000000 : ℝ)^1557 := by
    have hnat : (1042773119 : ℕ)^2069*100000000000000^1557 ≤ 31287705508573^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042773119 2500000000 31287705508573 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370424699/10000000000 : ℝ), (457945131/1000000000 : ℝ), (1042773119/2500000000 : ℝ)] ![(16645020578627/50000000000000 : ℝ), (4427781665541/12500000000000 : ℝ), (31287705508573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370424699/10000000000 : ℝ)|^2069 ≤ (16645020578627/50000000000000 : ℝ)^1557
        have hw : |(4370424699/10000000000 : ℝ)|=(4370424699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457945131/1000000000 : ℝ)|^2069 ≤ (4427781665541/12500000000000 : ℝ)^1557
        have hw : |(457945131/1000000000 : ℝ)|=(457945131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042773119/2500000000 : ℝ)|^2069 ≤ (31287705508573/100000000000000 : ℝ)^1557
        have hw : |(1042773119/2500000000 : ℝ)|=(1042773119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3337/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1759/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2613/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7441/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3337/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1759/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3337/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1759/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3337/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1759/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3337/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1759/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3337/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1759/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3337/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1759/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1759/20000 : ℝ) ^ (8275/2048 : ℝ) ≤ (5421956866470489/100000000000000000000 : ℝ) := by
    have hpowers : (1759/20000 : ℝ)^8275 ≤ (5421956866470489/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1759 : ℕ)^8275*100000000000000000000^2048 ≤ 5421956866470489^2048*20000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759 20000 5421956866470489 100000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1759/20000 : ℝ)) (X := (5421956866470489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3337/20000 : ℝ) ^ (8275/2048 : ℝ) ≤ (72075521101039681/100000000000000000000 : ℝ) := by
    have hpowers : (3337/20000 : ℝ)^8275 ≤ (72075521101039681/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3337 : ℕ)^8275*100000000000000000000^2048 ≤ 72075521101039681^2048*20000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3337 20000 72075521101039681 100000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3337/20000 : ℝ)) (X := (72075521101039681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005421956866470489/50000000000000000000 : ℝ) ≤ (10000268367725297/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (50005421956866470489/50000000000000000000 : ℝ)^2048 ≤ (10000268367725297/10000000000000000 : ℝ)^8275 := by
      have hnat : (50005421956866470489 : ℕ)^2048*10000000000000000^8275 ≤ 10000268367725297^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005421956866470489 50000000000000000000 10000268367725297 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000268367725297/10000000000000000 : ℝ)) (X := (50005421956866470489/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10007749747796751017/10000000000000000000 : ℝ) ≤ (5000958722517253/5000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (10007749747796751017/10000000000000000000 : ℝ)^2048 ≤ (5000958722517253/5000000000000000 : ℝ)^8275 := by
      have hnat : (10007749747796751017 : ℕ)^2048*5000000000000000^8275 ≤ 5000958722517253^8275*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007749747796751017 10000000000000000000 5000958722517253 5000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000958722517253/5000000000000000 : ℝ)) (X := (10007749747796751017/10000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50072075521101039681/50000000000000000000 : ℝ) ≤ (2000713304468743/2000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (50072075521101039681/50000000000000000000 : ℝ)^2048 ≤ (2000713304468743/2000000000000000 : ℝ)^8275 := by
      have hnat : (50072075521101039681 : ℕ)^2048*2000000000000000^8275 ≤ 2000713304468743^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50072075521101039681 50000000000000000000 2000713304468743 2000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000713304468743/2000000000000000 : ℝ)) (X := (50072075521101039681/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5421956866470489/100000000000000000000 : ℝ) ≤ ((1314551835858060117/1315000000000000000 : ℝ)+2*(549692436403/263000000000000 : ℝ)*(1759/20000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (1314551835858060117/1315000000000000000 : ℝ)+2*(549692436403/263000000000000 : ℝ)*(1759/20000 : ℝ)=(10000268367725297/10000000000000000 : ℝ) by norm_num, show 1+2*(5421956866470489/100000000000000000000 : ℝ)=(50005421956866470489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(72075521101039681/100000000000000000000 : ℝ)+(5421956866470489/100000000000000000000 : ℝ) ≤ ((1314551835858060117/1315000000000000000 : ℝ)+(549692436403/263000000000000 : ℝ)*((3337/20000 : ℝ)+(1759/20000 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (1314551835858060117/1315000000000000000 : ℝ)+(549692436403/263000000000000 : ℝ)*((3337/20000 : ℝ)+(1759/20000 : ℝ))=(5000958722517253/5000000000000000 : ℝ) by norm_num, show 1+(72075521101039681/100000000000000000000 : ℝ)+(5421956866470489/100000000000000000000 : ℝ)=(10007749747796751017/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(72075521101039681/100000000000000000000 : ℝ) ≤ ((1314551835858060117/1315000000000000000 : ℝ)+2*(549692436403/263000000000000 : ℝ)*(3337/20000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (1314551835858060117/1315000000000000000 : ℝ)+2*(549692436403/263000000000000 : ℝ)*(3337/20000 : ℝ)=(2000713304468743/2000000000000000 : ℝ) by norm_num, show 1+2*(72075521101039681/100000000000000000000 : ℝ)=(50072075521101039681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1314551835858060117/1315000000000000000 : ℝ)*(X 1 0+X 2 0)+(549692436403/263000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (1759/20000 : ℝ)) (hi := (3337/20000 : ℝ)) (c := (1314551835858060117/1315000000000000000 : ℝ)) (alpha := (549692436403/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1314551835858060117/1315000000000000000 : ℝ)*(X 0 1+X 2 1)+(549692436403/263000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (1759/20000 : ℝ)) (hi := (3337/20000 : ℝ)) (c := (1314551835858060117/1315000000000000000 : ℝ)) (alpha := (549692436403/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1314551835858060117/1315000000000000000 : ℝ)*(X 0 2+X 1 2)+(549692436403/263000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (1759/20000 : ℝ)) (hi := (3337/20000 : ℝ)) (c := (1314551835858060117/1315000000000000000 : ℝ)) (alpha := (549692436403/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190913079/10000000000 : ℝ)*X 0 0+(5435565543/10000000000 : ℝ)*X 0 1+(653275711/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355253031/10000000000 : ℝ)*X 1 0+(-1149038383/5000000000 : ℝ)*X 1 1+(5226205667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071050591/2000000000 : ℝ)*X 2 0+(1045241217/2000000000 : ℝ)*X 2 1+(-2298076319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370383109/10000000000 : ℝ)*X 0 0+(833883357/2000000000 : ℝ)*X 0 1+(572639633/1250000000 : ℝ)*X 0 2+(4370383109/10000000000 : ℝ)*X 1 0+(833883357/2000000000 : ℝ)*X 1 1+(572639633/1250000000 : ℝ)*X 1 2+(4370383109/10000000000 : ℝ)*X 2 0+(833883357/2000000000 : ℝ)*X 2 1+(572639633/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-547733619/2500000000 : ℝ)*X 0 0+(5227053271/10000000000 : ℝ)*X 0 1+(5434712923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302446413/10000000000 : ℝ)*X 1 0+(-417913871/2000000000 : ℝ)*X 1 1+(217388529/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662805823/1250000000 : ℝ)*X 2 0+(1086942591/2000000000 : ℝ)*X 2 1+(-522392373/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370424699/10000000000 : ℝ)*X 0 0+(457945131/1000000000 : ℝ)*X 0 1+(1042773119/2500000000 : ℝ)*X 0 2+(4370424699/10000000000 : ℝ)*X 1 0+(457945131/1000000000 : ℝ)*X 1 1+(1042773119/2500000000 : ℝ)*X 1 2+(4370424699/10000000000 : ℝ)*X 2 0+(457945131/1000000000 : ℝ)*X 2 1+(1042773119/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33270012797374364003159247/6575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58992961/4000000000000 : ℝ)*(base19) + (16114703/1562500000000 : ℝ)*(base23) + (40238967/20000000000000 : ℝ)*(lower2) + (29186217/100000000000000 : ℝ)*(upper3) + (169903481/100000000000000 : ℝ)*(upper5) + (360274749084703/10000000000000 : ℝ)*(major0) + (360274749084703/10000000000000 : ℝ)*(major1) + (360274749084703/10000000000000 : ℝ)*(major2) + (4776489234900811/100000000000000 : ℝ)*(sp0) + (477651964548099/10000000000000 : ℝ)*(sp1) + (4776520088964023/100000000000000 : ℝ)*(sp2) + (1214481446901461/50000000000000 : ℝ)*(sp3) + (31885404203/100000000000000 : ℝ)*(sp4) + (10798916849/100000000000000 : ℝ)*(sp7) + (2428973692719771/100000000000000 : ℝ)*(f.failure) + (2388260560152507/50000000000000 : ℝ)*(f.sum) + (819540408071/1315000000000000000000000000 : ℝ)*base66 + (144196588415735251/13150000000000000000000000000000 : ℝ)*base67 + (654555601714749/13150000000000000000000000000000 : ℝ)*base70 + (109430844987214749/13150000000000000000000000000000 : ℝ)*base72 + (5197371793009/1315000000000000000000000000 : ℝ)*base73 + (36268777190335251/13150000000000000000000000000000 : ℝ)*base75 + (154765051846535251/13150000000000000000000000000000 : ℝ)*base77 + (4727339033385251/13150000000000000000000000000000 : ℝ)*base79 + (328797935721/328750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (26201741/5000000000000000000000 : ℝ)*base90 + (26201741/5000000000000000000000 : ℝ)*base92 + (26201741/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168640472067851823550096431/16437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (477993593/25000000000000 : ℝ)*(base19) + (1176280343/50000000000000 : ℝ)*(base23) + (149942257/50000000000000 : ℝ)*(upper3) + (60672907/50000000000000 : ℝ)*(lower4) + (24018061/20000000000000 : ℝ)*(upper5) + (908049341391919/25000000000000 : ℝ)*(major0) + (908049341391919/25000000000000 : ℝ)*(major1) + (908049341391919/25000000000000 : ℝ)*(major2) + (1722759367/5000000000000 : ℝ)*(sp1) + (40122578977/100000000000000 : ℝ)*(sp2) + (4815565579988017/100000000000000 : ℝ)*(sp4) + (963105842565261/20000000000000 : ℝ)*(sp5) + (4815523104848353/100000000000000 : ℝ)*(sp6) + (2448828809164117/100000000000000 : ℝ)*(sp7) + (2448828809164117/100000000000000 : ℝ)*(f.failure) + (4815565579988017/100000000000000 : ℝ)*(f.sum) + (17113638886389/6575000000000000000000000000 : ℝ)*base65 + (22056843734595477/32875000000000000000000000000000 : ℝ)*base68 + (189292240880654523/32875000000000000000000000000000 : ℝ)*base69 + (147704711503779523/32875000000000000000000000000000 : ℝ)*base71 + (22805840830589/6575000000000000000000000000 : ℝ)*base73 + (43824243217095477/32875000000000000000000000000000 : ℝ)*base76 + (106417601208029523/32875000000000000000000000000000 : ℝ)*base77 + (94671282835529523/32875000000000000000000000000000 : ℝ)*base79 + (43857190608739/6575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5698307/5000000000000000000000 : ℝ)*base90 + (5698307/5000000000000000000000 : ℝ)*base92 + (5698307/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1083_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3337/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1759/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2613/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7441/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1083_s4_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097213669/5000000000 : ℝ)*x 0 + (5404888021/10000000000 : ℝ)*x 1 + (82102917/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097213669/5000000000 : ℝ)^2069 ≤ (13326708904077/100000000000000 : ℝ)^1557 := by
    have hnat : (1097213669 : ℕ)^2069*100000000000000^1557 ≤ 13326708904077^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097213669 5000000000 13326708904077 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404888021/10000000000 : ℝ)^2069 ≤ (4414860091147/10000000000000 : ℝ)^1557 := by
    have hnat : (5404888021 : ℕ)^2069*10000000000000^1557 ≤ 4414860091147^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404888021 10000000000 4414860091147 10000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82102917/156250000 : ℝ)^2069 ≤ (85049380351/200000000000 : ℝ)^1557 := by
    have hnat : (82102917 : ℕ)^2069*200000000000^1557 ≤ 85049380351^1557*156250000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82102917 156250000 85049380351 200000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097213669/5000000000 : ℝ), (5404888021/10000000000 : ℝ), (82102917/156250000 : ℝ)] ![(13326708904077/100000000000000 : ℝ), (4414860091147/10000000000000 : ℝ), (85049380351/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097213669/5000000000 : ℝ)|^2069 ≤ (13326708904077/100000000000000 : ℝ)^1557
        have hw : |(-1097213669/5000000000 : ℝ)|=(1097213669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404888021/10000000000 : ℝ)|^2069 ≤ (4414860091147/10000000000000 : ℝ)^1557
        have hw : |(5404888021/10000000000 : ℝ)|=(5404888021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82102917/156250000 : ℝ)|^2069 ≤ (85049380351/200000000000 : ℝ)^1557
        have hw : |(82102917/156250000 : ℝ)|=(82102917/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668454979/1250000000 : ℝ)*x 0 + (-2270857243/10000000000 : ℝ)*x 1 + (5254587651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668454979/1250000000 : ℝ)^2069 ≤ (21764148097251/50000000000000 : ℝ)^1557 := by
    have hnat : (668454979 : ℕ)^2069*50000000000000^1557 ≤ 21764148097251^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668454979 1250000000 21764148097251 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270857243/10000000000 : ℝ)^2069 ≤ (6973501629087/50000000000000 : ℝ)^1557 := by
    have hnat : (2270857243 : ℕ)^2069*50000000000000^1557 ≤ 6973501629087^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270857243 10000000000 6973501629087 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254587651/10000000000 : ℝ)^2069 ≤ (10631175132927/25000000000000 : ℝ)^1557 := by
    have hnat : (5254587651 : ℕ)^2069*25000000000000^1557 ≤ 10631175132927^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254587651 10000000000 10631175132927 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668454979/1250000000 : ℝ), (-2270857243/10000000000 : ℝ), (5254587651/10000000000 : ℝ)] ![(21764148097251/50000000000000 : ℝ), (6973501629087/50000000000000 : ℝ), (10631175132927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668454979/1250000000 : ℝ)|^2069 ≤ (21764148097251/50000000000000 : ℝ)^1557
        have hw : |(668454979/1250000000 : ℝ)|=(668454979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2270857243/10000000000 : ℝ)|^2069 ≤ (6973501629087/50000000000000 : ℝ)^1557
        have hw : |(-2270857243/10000000000 : ℝ)|=(2270857243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254587651/10000000000 : ℝ)|^2069 ≤ (10631175132927/25000000000000 : ℝ)^1557
        have hw : |(5254587651/10000000000 : ℝ)|=(5254587651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673820151/5000000000 : ℝ)*x 0 + (210183483/400000000 : ℝ)*x 1 + (-2270857379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673820151/5000000000 : ℝ)^2069 ≤ (8705660255639/20000000000000 : ℝ)^1557 := by
    have hnat : (2673820151 : ℕ)^2069*20000000000000^1557 ≤ 8705660255639^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673820151 5000000000 8705660255639 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210183483/400000000 : ℝ)^2069 ≤ (42524694337341/100000000000000 : ℝ)^1557 := by
    have hnat : (210183483 : ℕ)^2069*100000000000000^1557 ≤ 42524694337341^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210183483 400000000 42524694337341 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270857379/10000000000 : ℝ)^2069 ≤ (348675109203/2500000000000 : ℝ)^1557 := by
    have hnat : (2270857379 : ℕ)^2069*2500000000000^1557 ≤ 348675109203^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270857379 10000000000 348675109203 2500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673820151/5000000000 : ℝ), (210183483/400000000 : ℝ), (-2270857379/10000000000 : ℝ)] ![(8705660255639/20000000000000 : ℝ), (42524694337341/100000000000000 : ℝ), (348675109203/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673820151/5000000000 : ℝ)|^2069 ≤ (8705660255639/20000000000000 : ℝ)^1557
        have hw : |(2673820151/5000000000 : ℝ)|=(2673820151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210183483/400000000 : ℝ)|^2069 ≤ (42524694337341/100000000000000 : ℝ)^1557
        have hw : |(210183483/400000000 : ℝ)|=(210183483/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2270857379/10000000000 : ℝ)|^2069 ≤ (348675109203/2500000000000 : ℝ)^1557
        have hw : |(-2270857379/10000000000 : ℝ)|=(2270857379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4372474679/10000000000 : ℝ)*x 0 + (1056802913/2500000000 : ℝ)*x 1 + (2261387503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372474679/10000000000 : ℝ)^2069 ≤ (33310792475033/100000000000000 : ℝ)^1557 := by
    have hnat : (4372474679 : ℕ)^2069*100000000000000^1557 ≤ 33310792475033^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372474679 10000000000 33310792475033 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056802913/2500000000 : ℝ)^2069 ≤ (3981039924319/12500000000000 : ℝ)^1557 := by
    have hnat : (1056802913 : ℕ)^2069*12500000000000^1557 ≤ 3981039924319^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056802913 2500000000 3981039924319 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261387503/5000000000 : ℝ)^2069 ≤ (34840888120629/100000000000000 : ℝ)^1557 := by
    have hnat : (2261387503 : ℕ)^2069*100000000000000^1557 ≤ 34840888120629^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261387503 5000000000 34840888120629 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372474679/10000000000 : ℝ), (1056802913/2500000000 : ℝ), (2261387503/5000000000 : ℝ)] ![(33310792475033/100000000000000 : ℝ), (3981039924319/12500000000000 : ℝ), (34840888120629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372474679/10000000000 : ℝ)|^2069 ≤ (33310792475033/100000000000000 : ℝ)^1557
        have hw : |(4372474679/10000000000 : ℝ)|=(4372474679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056802913/2500000000 : ℝ)|^2069 ≤ (3981039924319/12500000000000 : ℝ)^1557
        have hw : |(1056802913/2500000000 : ℝ)|=(1056802913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261387503/5000000000 : ℝ)|^2069 ≤ (34840888120629/100000000000000 : ℝ)^1557
        have hw : |(2261387503/5000000000 : ℝ)|=(2261387503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-548608417/2500000000 : ℝ)*x 0 + (2627512539/5000000000 : ℝ)*x 1 + (5404448959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548608417/2500000000 : ℝ)^2069 ≤ (13326759987207/100000000000000 : ℝ)^1557 := by
    have hnat : (548608417 : ℕ)^2069*100000000000000^1557 ≤ 13326759987207^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548608417 2500000000 13326759987207 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627512539/5000000000 : ℝ)^2069 ≤ (42529404734459/100000000000000 : ℝ)^1557 := by
    have hnat : (2627512539 : ℕ)^2069*100000000000000^1557 ≤ 42529404734459^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627512539 5000000000 42529404734459 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404448959/10000000000 : ℝ)^2069 ≤ (8828767052229/20000000000000 : ℝ)^1557 := by
    have hnat : (5404448959 : ℕ)^2069*20000000000000^1557 ≤ 8828767052229^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404448959 10000000000 8828767052229 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548608417/2500000000 : ℝ), (2627512539/5000000000 : ℝ), (5404448959/10000000000 : ℝ)] ![(13326759987207/100000000000000 : ℝ), (42529404734459/100000000000000 : ℝ), (8828767052229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548608417/2500000000 : ℝ)|^2069 ≤ (13326759987207/100000000000000 : ℝ)^1557
        have hw : |(-548608417/2500000000 : ℝ)|=(548608417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627512539/5000000000 : ℝ)|^2069 ≤ (42529404734459/100000000000000 : ℝ)^1557
        have hw : |(2627512539/5000000000 : ℝ)|=(2627512539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404448959/10000000000 : ℝ)|^2069 ≤ (8828767052229/20000000000000 : ℝ)^1557
        have hw : |(5404448959/10000000000 : ℝ)|=(5404448959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5309733519/10000000000 : ℝ)*x 0 + (-265124421/1250000000 : ℝ)*x 1 + (5404449003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309733519/10000000000 : ℝ)^2069 ≤ (43118766230579/100000000000000 : ℝ)^1557 := by
    have hnat : (5309733519 : ℕ)^2069*100000000000000^1557 ≤ 43118766230579^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309733519 10000000000 43118766230579 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265124421/1250000000 : ℝ)^2069 ≤ (12737398018397/100000000000000 : ℝ)^1557 := by
    have hnat : (265124421 : ℕ)^2069*100000000000000^1557 ≤ 12737398018397^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265124421 1250000000 12737398018397 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404449003/10000000000 : ℝ)^2069 ≤ (22071917869361/50000000000000 : ℝ)^1557 := by
    have hnat : (5404449003 : ℕ)^2069*50000000000000^1557 ≤ 22071917869361^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404449003 10000000000 22071917869361 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309733519/10000000000 : ℝ), (-265124421/1250000000 : ℝ), (5404449003/10000000000 : ℝ)] ![(43118766230579/100000000000000 : ℝ), (12737398018397/100000000000000 : ℝ), (22071917869361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309733519/10000000000 : ℝ)|^2069 ≤ (43118766230579/100000000000000 : ℝ)^1557
        have hw : |(5309733519/10000000000 : ℝ)|=(5309733519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265124421/1250000000 : ℝ)|^2069 ≤ (12737398018397/100000000000000 : ℝ)^1557
        have hw : |(-265124421/1250000000 : ℝ)|=(265124421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404449003/10000000000 : ℝ)|^2069 ≤ (22071917869361/50000000000000 : ℝ)^1557
        have hw : |(5404449003/10000000000 : ℝ)|=(5404449003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5309733399/10000000000 : ℝ)*x 0 + (2702224433/5000000000 : ℝ)*x 1 + (-424199143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309733399/10000000000 : ℝ)^2069 ≤ (1347461404239/3125000000000 : ℝ)^1557 := by
    have hnat : (5309733399 : ℕ)^2069*3125000000000^1557 ≤ 1347461404239^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309733399 10000000000 1347461404239 3125000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702224433/5000000000 : ℝ)^2069 ≤ (22071917125861/50000000000000 : ℝ)^1557 := by
    have hnat : (2702224433 : ℕ)^2069*50000000000000^1557 ≤ 22071917125861^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702224433 5000000000 22071917125861 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424199143/2000000000 : ℝ)^2069 ≤ (12737400787521/100000000000000 : ℝ)^1557 := by
    have hnat : (424199143 : ℕ)^2069*100000000000000^1557 ≤ 12737400787521^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424199143 2000000000 12737400787521 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309733399/10000000000 : ℝ), (2702224433/5000000000 : ℝ), (-424199143/2000000000 : ℝ)] ![(1347461404239/3125000000000 : ℝ), (22071917125861/50000000000000 : ℝ), (12737400787521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309733399/10000000000 : ℝ)|^2069 ≤ (1347461404239/3125000000000 : ℝ)^1557
        have hw : |(5309733399/10000000000 : ℝ)|=(5309733399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702224433/5000000000 : ℝ)|^2069 ≤ (22071917125861/50000000000000 : ℝ)^1557
        have hw : |(2702224433/5000000000 : ℝ)|=(2702224433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424199143/2000000000 : ℝ)|^2069 ≤ (12737400787521/100000000000000 : ℝ)^1557
        have hw : |(-424199143/2000000000 : ℝ)|=(424199143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2186245039/5000000000 : ℝ)*x 0 + (2260957217/5000000000 : ℝ)*x 1 + (845615187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186245039/5000000000 : ℝ)^2069 ≤ (4163868545811/12500000000000 : ℝ)^1557 := by
    have hnat : (2186245039 : ℕ)^2069*12500000000000^1557 ≤ 4163868545811^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186245039 5000000000 4163868545811 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260957217/5000000000 : ℝ)^2069 ≤ (2177004941077/6250000000000 : ℝ)^1557 := by
    have hnat : (2260957217 : ℕ)^2069*6250000000000^1557 ≤ 2177004941077^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260957217 5000000000 2177004941077 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845615187/2000000000 : ℝ)^2069 ≤ (1592848627967/5000000000000 : ℝ)^1557 := by
    have hnat : (845615187 : ℕ)^2069*5000000000000^1557 ≤ 1592848627967^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845615187 2000000000 1592848627967 5000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186245039/5000000000 : ℝ), (2260957217/5000000000 : ℝ), (845615187/2000000000 : ℝ)] ![(4163868545811/12500000000000 : ℝ), (2177004941077/6250000000000 : ℝ), (1592848627967/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186245039/5000000000 : ℝ)|^2069 ≤ (4163868545811/12500000000000 : ℝ)^1557
        have hw : |(2186245039/5000000000 : ℝ)|=(2186245039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2260957217/5000000000 : ℝ)|^2069 ≤ (2177004941077/6250000000000 : ℝ)^1557
        have hw : |(2260957217/5000000000 : ℝ)|=(2260957217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845615187/2000000000 : ℝ)|^2069 ≤ (1592848627967/5000000000000 : ℝ)^1557
        have hw : |(845615187/2000000000 : ℝ)|=(845615187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_8 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-17995977/10000000000 : ℝ)*x 0 + (5934596899/10000000000 : ℝ)*x 1 + (237382583/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17995977/10000000000 : ℝ)^2069 ≤ (22520299279/100000000000000 : ℝ)^1557 := by
    have hnat : (17995977 : ℕ)^2069*100000000000000^1557 ≤ 22520299279^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17995977 10000000000 22520299279 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5934596899/10000000000 : ℝ)^2069 ≤ (12497230188089/25000000000000 : ℝ)^1557 := by
    have hnat : (5934596899 : ℕ)^2069*25000000000000^1557 ≤ 12497230188089^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5934596899 10000000000 12497230188089 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237382583/400000000 : ℝ)^2069 ≤ (49988558943559/100000000000000 : ℝ)^1557 := by
    have hnat : (237382583 : ℕ)^2069*100000000000000^1557 ≤ 49988558943559^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237382583 400000000 49988558943559 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17995977/10000000000 : ℝ), (5934596899/10000000000 : ℝ), (237382583/400000000 : ℝ)] ![(22520299279/100000000000000 : ℝ), (12497230188089/25000000000000 : ℝ), (49988558943559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17995977/10000000000 : ℝ)|^2069 ≤ (22520299279/100000000000000 : ℝ)^1557
        have hw : |(-17995977/10000000000 : ℝ)|=(17995977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5934596899/10000000000 : ℝ)|^2069 ≤ (12497230188089/25000000000000 : ℝ)^1557
        have hw : |(5934596899/10000000000 : ℝ)|=(5934596899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237382583/400000000 : ℝ)|^2069 ≤ (49988558943559/100000000000000 : ℝ)^1557
        have hw : |(237382583/400000000 : ℝ)|=(237382583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s4_9 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (347496837/2500000000 : ℝ)*x 0 + (1121541169/2000000000 : ℝ)*x 1 + (5608483893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (347496837/2500000000 : ℝ)^2069 ≤ (1452883077961/20000000000000 : ℝ)^1557 := by
    have hnat : (347496837 : ℕ)^2069*20000000000000^1557 ≤ 1452883077961^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347496837 2500000000 1452883077961 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121541169/2000000000 : ℝ)^2069 ≤ (46363518152907/100000000000000 : ℝ)^1557 := by
    have hnat : (1121541169 : ℕ)^2069*100000000000000^1557 ≤ 46363518152907^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121541169 2000000000 46363518152907 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5608483893/10000000000 : ℝ)^2069 ≤ (9274413288927/20000000000000 : ℝ)^1557 := by
    have hnat : (5608483893 : ℕ)^2069*20000000000000^1557 ≤ 9274413288927^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608483893 10000000000 9274413288927 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(347496837/2500000000 : ℝ), (1121541169/2000000000 : ℝ), (5608483893/10000000000 : ℝ)] ![(1452883077961/20000000000000 : ℝ), (46363518152907/100000000000000 : ℝ), (9274413288927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(347496837/2500000000 : ℝ)|^2069 ≤ (1452883077961/20000000000000 : ℝ)^1557
        have hw : |(347496837/2500000000 : ℝ)|=(347496837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121541169/2000000000 : ℝ)|^2069 ≤ (46363518152907/100000000000000 : ℝ)^1557
        have hw : |(1121541169/2000000000 : ℝ)|=(1121541169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5608483893/10000000000 : ℝ)|^2069 ≤ (9274413288927/20000000000000 : ℝ)^1557
        have hw : |(5608483893/10000000000 : ℝ)|=(5608483893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7441/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2613/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5529/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7441/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2613/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7441/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2613/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7441/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2613/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7441/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2613/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7441/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2613/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7441/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2613/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2613/25000 : ℝ) ^ (8275/2048 : ℝ) ≤ (5445256793684119/50000000000000000000 : ℝ) := by
    have hpowers : (2613/25000 : ℝ)^8275 ≤ (5445256793684119/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2613 : ℕ)^8275*50000000000000000000^2048 ≤ 5445256793684119^2048*25000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2613 25000 5445256793684119 50000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2613/25000 : ℝ)) (X := (5445256793684119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7441/50000 : ℝ) ^ (8275/2048 : ℝ) ≤ (22703110621190653/50000000000000000000 : ℝ) := by
    have hpowers : (7441/50000 : ℝ)^8275 ≤ (22703110621190653/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7441 : ℕ)^8275*50000000000000000000^2048 ≤ 22703110621190653^2048*50000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7441 50000 22703110621190653 50000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7441/50000 : ℝ)) (X := (22703110621190653/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005445256793684119/25000000000000000000 : ℝ) ≤ (2500134754949983/2500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (25005445256793684119/25000000000000000000 : ℝ)^2048 ≤ (2500134754949983/2500000000000000 : ℝ)^8275 := by
      have hnat : (25005445256793684119 : ℕ)^2048*2500000000000000^8275 ≤ 2500134754949983^8275*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005445256793684119 25000000000000000000 2500134754949983 2500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134754949983/2500000000000000 : ℝ)) (X := (25005445256793684119/25000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507037091853718693/12500000000000000000 : ℝ) ≤ (10001393006636669/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (12507037091853718693/12500000000000000000 : ℝ)^2048 ≤ (10001393006636669/10000000000000000 : ℝ)^8275 := by
      have hnat : (12507037091853718693 : ℕ)^2048*10000000000000000^8275 ≤ 10001393006636669^8275*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507037091853718693 12500000000000000000 10001393006636669 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001393006636669/10000000000000000 : ℝ)) (X := (12507037091853718693/12500000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022703110621190653/25000000000000000000 : ℝ) ≤ (5001123496736703/5000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (25022703110621190653/25000000000000000000 : ℝ)^2048 ≤ (5001123496736703/5000000000000000 : ℝ)^8275 := by
      have hnat : (25022703110621190653 : ℕ)^2048*5000000000000000^8275 ≤ 5001123496736703^8275*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022703110621190653 25000000000000000000 5001123496736703 5000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001123496736703/5000000000000000 : ℝ)) (X := (25022703110621190653/25000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5445256793684119/50000000000000000000 : ℝ) ≤ ((1383891753652454641/1384375000000000000 : ℝ)+2*(853986836737/443000000000000 : ℝ)*(2613/25000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (1383891753652454641/1384375000000000000 : ℝ)+2*(853986836737/443000000000000 : ℝ)*(2613/25000 : ℝ)=(2500134754949983/2500000000000000 : ℝ) by norm_num, show 1+2*(5445256793684119/50000000000000000000 : ℝ)=(25005445256793684119/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22703110621190653/50000000000000000000 : ℝ)+(5445256793684119/50000000000000000000 : ℝ) ≤ ((1383891753652454641/1384375000000000000 : ℝ)+(853986836737/443000000000000 : ℝ)*((7441/50000 : ℝ)+(2613/25000 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (1383891753652454641/1384375000000000000 : ℝ)+(853986836737/443000000000000 : ℝ)*((7441/50000 : ℝ)+(2613/25000 : ℝ))=(10001393006636669/10000000000000000 : ℝ) by norm_num, show 1+(22703110621190653/50000000000000000000 : ℝ)+(5445256793684119/50000000000000000000 : ℝ)=(12507037091853718693/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22703110621190653/50000000000000000000 : ℝ) ≤ ((1383891753652454641/1384375000000000000 : ℝ)+2*(853986836737/443000000000000 : ℝ)*(7441/50000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (1383891753652454641/1384375000000000000 : ℝ)+2*(853986836737/443000000000000 : ℝ)*(7441/50000 : ℝ)=(5001123496736703/5000000000000000 : ℝ) by norm_num, show 1+2*(22703110621190653/50000000000000000000 : ℝ)=(25022703110621190653/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1383891753652454641/1384375000000000000 : ℝ)*(X 1 0+X 2 0)+(853986836737/443000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (2613/25000 : ℝ)) (hi := (7441/50000 : ℝ)) (c := (1383891753652454641/1384375000000000000 : ℝ)) (alpha := (853986836737/443000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1383891753652454641/1384375000000000000 : ℝ)*(X 0 1+X 2 1)+(853986836737/443000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (2613/25000 : ℝ)) (hi := (7441/50000 : ℝ)) (c := (1383891753652454641/1384375000000000000 : ℝ)) (alpha := (853986836737/443000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1383891753652454641/1384375000000000000 : ℝ)*(X 0 2+X 1 2)+(853986836737/443000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (2613/25000 : ℝ)) (hi := (7441/50000 : ℝ)) (c := (1383891753652454641/1384375000000000000 : ℝ)) (alpha := (853986836737/443000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1097213669/5000000000 : ℝ)*X 0 0+(5404888021/10000000000 : ℝ)*X 0 1+(82102917/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668454979/1250000000 : ℝ)*X 1 0+(-2270857243/10000000000 : ℝ)*X 1 1+(5254587651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673820151/5000000000 : ℝ)*X 2 0+(210183483/400000000 : ℝ)*X 2 1+(-2270857379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372474679/10000000000 : ℝ)*X 0 0+(1056802913/2500000000 : ℝ)*X 0 1+(2261387503/5000000000 : ℝ)*X 0 2+(4372474679/10000000000 : ℝ)*X 1 0+(1056802913/2500000000 : ℝ)*X 1 1+(2261387503/5000000000 : ℝ)*X 1 2+(4372474679/10000000000 : ℝ)*X 2 0+(1056802913/2500000000 : ℝ)*X 2 1+(2261387503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548608417/2500000000 : ℝ)*X 0 0+(2627512539/5000000000 : ℝ)*X 0 1+(5404448959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309733519/10000000000 : ℝ)*X 1 0+(-265124421/1250000000 : ℝ)*X 1 1+(5404449003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309733399/10000000000 : ℝ)*X 2 0+(2702224433/5000000000 : ℝ)*X 2 1+(-424199143/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186245039/5000000000 : ℝ)*X 0 0+(2260957217/5000000000 : ℝ)*X 0 1+(845615187/2000000000 : ℝ)*X 0 2+(2186245039/5000000000 : ℝ)*X 1 0+(2260957217/5000000000 : ℝ)*X 1 1+(845615187/2000000000 : ℝ)*X 1 2+(2186245039/5000000000 : ℝ)*X 2 0+(2260957217/5000000000 : ℝ)*X 2 1+(845615187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-17995977/10000000000 : ℝ)*X 0 0+(5934596899/10000000000 : ℝ)*X 0 1+(237382583/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((347496837/2500000000 : ℝ)*X 0 0+(1121541169/2000000000 : ℝ)*X 0 1+(5608483893/10000000000 : ℝ)*X 0 2+(347496837/2500000000 : ℝ)*X 1 0+(1121541169/2000000000 : ℝ)*X 1 1+(5608483893/10000000000 : ℝ)*X 1 2+(347496837/2500000000 : ℝ)*X 2 0+(1121541169/2000000000 : ℝ)*X 2 1+(5608483893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s4_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55810524938556836412457659/8652343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (303688627/100000000000000 : ℝ)*(lower2) + (413936487/100000000000000 : ℝ)*(lower5) + (1254588743424991/25000000000000 : ℝ)*(major0) + (1254588743424991/25000000000000 : ℝ)*(major1) + (1254588743424991/25000000000000 : ℝ)*(major2) + (3326657769694553/50000000000000 : ℝ)*(sp0) + (6653332950414787/100000000000000 : ℝ)*(sp1) + (6653330571424343/100000000000000 : ℝ)*(sp2) + (84584153721207/2500000000000 : ℝ)*(sp3) + (5123366197/50000000000000 : ℝ)*(sp4) + (475798089/20000000000000 : ℝ)*(sp6) + (8981395759/100000000000000 : ℝ)*(sp7) + (7164293287/100000000000000 : ℝ)*(sp8) + (825864939/50000000000000 : ℝ)*(sp9) + (1691688390986959/50000000000000 : ℝ)*(f.failure) + (6653332950414787/100000000000000 : ℝ)*(f.sum) + (30700533163209/11075000000000000000000000000 : ℝ)*base65 + (1531958458297214481/34609375000000000000000000000000 : ℝ)*base67 + (117297769723743607/4326171875000000000000000000000 : ℝ)*base69 + (98446577881340911/8652343750000000000000000000000 : ℝ)*base72 + (268745756109/11075000000000000000000000000 : ℝ)*base73 + (105545847758697447/17304687500000000000000000000000 : ℝ)*base76 + (2539776891380910519/34609375000000000000000000000000 : ℝ)*base78 + (8652228572473019/34609375000000000000000000000000 : ℝ)*base80 + (106001155074709/11075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6716089/2500000000000000000000 : ℝ)*base90 + (6716089/2500000000000000000000 : ℝ)*base92 + (6716089/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79420100756279183987261127/34609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11065671/4000000000000 : ℝ)*(lower3) + (8190049/6250000000000 : ℝ)*(lower4) + (102846969/50000000000000 : ℝ)*(lower5) + (1261949614954579/25000000000000 : ℝ)*(major0) + (1261949614954579/25000000000000 : ℝ)*(major1) + (1261949614954579/25000000000000 : ℝ)*(major2) + (3298845917/20000000000000 : ℝ)*(sp1) + (777641409/25000000000000 : ℝ)*(sp2) + (334618407039057/5000000000000 : ℝ)*(sp4) + (3346176378847457/50000000000000 : ℝ)*(sp5) + (6692366141358863/100000000000000 : ℝ)*(sp6) + (3403226528182819/100000000000000 : ℝ)*(sp7) + (3472323/312500000000 : ℝ)*(sp8) + (265759353/25000000000000 : ℝ)*(sp9) + (3403227591220231/100000000000000 : ℝ)*(f.failure) + (6692369251924499/100000000000000 : ℝ)*(f.sum) + (1217149154613/1384375000000000000000000000 : ℝ)*base66 + (22496538378864559/8652343750000000000000000000000 : ℝ)*base68 + (343209757123661361/34609375000000000000000000000000 : ℝ)*base70 + (57553393426244743/17304687500000000000000000000000 : ℝ)*base72 + (21193719512521/11075000000000000000000000000 : ℝ)*base73 + (78214509601833309/8652343750000000000000000000000 : ℝ)*base76 + (470378089046942611/34609375000000000000000000000000 : ℝ)*base78 + (146991828031713493/17304687500000000000000000000000 : ℝ)*base80 + (6449644646977/5537500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5214401/5000000000000000000000 : ℝ)*base90 + (5214401/5000000000000000000000 : ℝ)*base92 + (5214401/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1083_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7441/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2613/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1083_s5_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195211453/10000000000 : ℝ)*x 0 + (134912789/250000000 : ℝ)*x 1 + (2631224331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195211453/10000000000 : ℝ)^2069 ≤ (1666629635573/12500000000000 : ℝ)^1557 := by
    have hnat : (2195211453 : ℕ)^2069*12500000000000^1557 ≤ 1666629635573^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195211453 10000000000 1666629635573 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134912789/250000000 : ℝ)^2069 ≤ (22028851701827/50000000000000 : ℝ)^1557 := by
    have hnat : (134912789 : ℕ)^2069*50000000000000^1557 ≤ 22028851701827^1557*250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134912789 250000000 22028851701827 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631224331/5000000000 : ℝ)^2069 ≤ (10652314875313/25000000000000 : ℝ)^1557 := by
    have hnat : (2631224331 : ℕ)^2069*25000000000000^1557 ≤ 10652314875313^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631224331 5000000000 10652314875313 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195211453/10000000000 : ℝ), (134912789/250000000 : ℝ), (2631224331/5000000000 : ℝ)] ![(1666629635573/12500000000000 : ℝ), (22028851701827/50000000000000 : ℝ), (10652314875313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195211453/10000000000 : ℝ)|^2069 ≤ (1666629635573/12500000000000 : ℝ)^1557
        have hw : |(-2195211453/10000000000 : ℝ)|=(2195211453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134912789/250000000 : ℝ)|^2069 ≤ (22028851701827/50000000000000 : ℝ)^1557
        have hw : |(134912789/250000000 : ℝ)|=(134912789/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631224331/5000000000 : ℝ)|^2069 ≤ (10652314875313/25000000000000 : ℝ)^1557
        have hw : |(2631224331/5000000000 : ℝ)|=(2631224331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s5_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345549383/10000000000 : ℝ)*x 0 + (-2263262289/10000000000 : ℝ)*x 1 + (657806103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345549383/10000000000 : ℝ)^2069 ≤ (5438210823157/12500000000000 : ℝ)^1557 := by
    have hnat : (5345549383 : ℕ)^2069*12500000000000^1557 ≤ 5438210823157^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345549383 10000000000 5438210823157 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263262289/10000000000 : ℝ)^2069 ≤ (6942526078511/50000000000000 : ℝ)^1557 := by
    have hnat : (2263262289 : ℕ)^2069*50000000000000^1557 ≤ 6942526078511^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263262289 10000000000 6942526078511 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657806103/1250000000 : ℝ)^2069 ≤ (1704370449771/4000000000000 : ℝ)^1557 := by
    have hnat : (657806103 : ℕ)^2069*4000000000000^1557 ≤ 1704370449771^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657806103 1250000000 1704370449771 4000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345549383/10000000000 : ℝ), (-2263262289/10000000000 : ℝ), (657806103/1250000000 : ℝ)] ![(5438210823157/12500000000000 : ℝ), (6942526078511/50000000000000 : ℝ), (1704370449771/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345549383/10000000000 : ℝ)|^2069 ≤ (5438210823157/12500000000000 : ℝ)^1557
        have hw : |(5345549383/10000000000 : ℝ)|=(5345549383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263262289/10000000000 : ℝ)|^2069 ≤ (6942526078511/50000000000000 : ℝ)^1557
        have hw : |(-2263262289/10000000000 : ℝ)|=(2263262289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657806103/1250000000 : ℝ)|^2069 ≤ (1704370449771/4000000000000 : ℝ)^1557
        have hw : |(657806103/1250000000 : ℝ)|=(657806103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s5_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672774771/5000000000 : ℝ)*x 0 + (657806153/1250000000 : ℝ)*x 1 + (-45265231/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672774771/5000000000 : ℝ)^2069 ≤ (43505688304837/100000000000000 : ℝ)^1557 := by
    have hnat : (2672774771 : ℕ)^2069*100000000000000^1557 ≤ 43505688304837^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672774771 5000000000 43505688304837 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657806153/1250000000 : ℝ)^2069 ≤ (21304632774017/50000000000000 : ℝ)^1557 := by
    have hnat : (657806153 : ℕ)^2069*50000000000000^1557 ≤ 21304632774017^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657806153 1250000000 21304632774017 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45265231/200000000 : ℝ)^2069 ≤ (3471261533103/25000000000000 : ℝ)^1557 := by
    have hnat : (45265231 : ℕ)^2069*25000000000000^1557 ≤ 3471261533103^1557*200000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45265231 200000000 3471261533103 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672774771/5000000000 : ℝ), (657806153/1250000000 : ℝ), (-45265231/200000000 : ℝ)] ![(43505688304837/100000000000000 : ℝ), (21304632774017/50000000000000 : ℝ), (3471261533103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672774771/5000000000 : ℝ)|^2069 ≤ (43505688304837/100000000000000 : ℝ)^1557
        have hw : |(2672774771/5000000000 : ℝ)|=(2672774771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657806153/1250000000 : ℝ)|^2069 ≤ (21304632774017/50000000000000 : ℝ)^1557
        have hw : |(657806153/1250000000 : ℝ)|=(657806153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45265231/200000000 : ℝ)|^2069 ≤ (3471261533103/25000000000000 : ℝ)^1557
        have hw : |(-45265231/200000000 : ℝ)|=(45265231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s5_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2186464897/5000000000 : ℝ)*x 0 + (4243118609/10000000000 : ℝ)*x 1 + (70417947/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186464897/5000000000 : ℝ)^2069 ≤ (3331539989841/10000000000000 : ℝ)^1557 := by
    have hnat : (2186464897 : ℕ)^2069*10000000000000^1557 ≤ 3331539989841^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186464897 5000000000 3331539989841 10000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243118609/10000000000 : ℝ)^2069 ≤ (2000479516863/6250000000000 : ℝ)^1557 := by
    have hnat : (4243118609 : ℕ)^2069*6250000000000^1557 ≤ 2000479516863^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243118609 10000000000 2000479516863 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70417947/156250000 : ℝ)^2069 ≤ (8669231952369/25000000000000 : ℝ)^1557 := by
    have hnat : (70417947 : ℕ)^2069*25000000000000^1557 ≤ 8669231952369^1557*156250000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70417947 156250000 8669231952369 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186464897/5000000000 : ℝ), (4243118609/10000000000 : ℝ), (70417947/156250000 : ℝ)] ![(3331539989841/10000000000000 : ℝ), (2000479516863/6250000000000 : ℝ), (8669231952369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186464897/5000000000 : ℝ)|^2069 ≤ (3331539989841/10000000000000 : ℝ)^1557
        have hw : |(2186464897/5000000000 : ℝ)|=(2186464897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243118609/10000000000 : ℝ)|^2069 ≤ (2000479516863/6250000000000 : ℝ)^1557
        have hw : |(4243118609/10000000000 : ℝ)|=(4243118609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70417947/156250000 : ℝ)|^2069 ≤ (8669231952369/25000000000000 : ℝ)^1557
        have hw : |(70417947/156250000 : ℝ)|=(70417947/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s5_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-548804207/2500000000 : ℝ)*x 0 + (2631398647/5000000000 : ℝ)*x 1 + (5396161793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548804207/2500000000 : ℝ)^2069 ≤ (13333080465953/100000000000000 : ℝ)^1557 := by
    have hnat : (548804207 : ℕ)^2069*100000000000000^1557 ≤ 13333080465953^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548804207 2500000000 13333080465953 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631398647/5000000000 : ℝ)^2069 ≤ (21306505306363/50000000000000 : ℝ)^1557 := by
    have hnat : (2631398647 : ℕ)^2069*50000000000000^1557 ≤ 21306505306363^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631398647 5000000000 21306505306363 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396161793/10000000000 : ℝ)^2069 ≤ (44053908901313/100000000000000 : ℝ)^1557 := by
    have hnat : (5396161793 : ℕ)^2069*100000000000000^1557 ≤ 44053908901313^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396161793 10000000000 44053908901313 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548804207/2500000000 : ℝ), (2631398647/5000000000 : ℝ), (5396161793/10000000000 : ℝ)] ![(13333080465953/100000000000000 : ℝ), (21306505306363/50000000000000 : ℝ), (44053908901313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548804207/2500000000 : ℝ)|^2069 ≤ (13333080465953/100000000000000 : ℝ)^1557
        have hw : |(-548804207/2500000000 : ℝ)|=(548804207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631398647/5000000000 : ℝ)|^2069 ≤ (21306505306363/50000000000000 : ℝ)^1557
        have hw : |(2631398647/5000000000 : ℝ)|=(2631398647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396161793/10000000000 : ℝ)|^2069 ≤ (44053908901313/100000000000000 : ℝ)^1557
        have hw : |(5396161793/10000000000 : ℝ)|=(5396161793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s5_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311737129/10000000000 : ℝ)*x 0 + (-1064774471/5000000000 : ℝ)*x 1 + (5396161797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311737129/10000000000 : ℝ)^2069 ≤ (8628077743177/20000000000000 : ℝ)^1557 := by
    have hnat : (5311737129 : ℕ)^2069*20000000000000^1557 ≤ 8628077743177^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311737129 10000000000 8628077743177 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064774471/5000000000 : ℝ)^2069 ≤ (6402851164141/50000000000000 : ℝ)^1557 := by
    have hnat : (1064774471 : ℕ)^2069*50000000000000^1557 ≤ 6402851164141^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064774471 5000000000 6402851164141 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396161797/10000000000 : ℝ)^2069 ≤ (44053908944707/100000000000000 : ℝ)^1557 := by
    have hnat : (5396161797 : ℕ)^2069*100000000000000^1557 ≤ 44053908944707^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396161797 10000000000 44053908944707 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311737129/10000000000 : ℝ), (-1064774471/5000000000 : ℝ), (5396161797/10000000000 : ℝ)] ![(8628077743177/20000000000000 : ℝ), (6402851164141/50000000000000 : ℝ), (44053908944707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311737129/10000000000 : ℝ)|^2069 ≤ (8628077743177/20000000000000 : ℝ)^1557
        have hw : |(5311737129/10000000000 : ℝ)|=(5311737129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064774471/5000000000 : ℝ)|^2069 ≤ (6402851164141/50000000000000 : ℝ)^1557
        have hw : |(-1064774471/5000000000 : ℝ)|=(1064774471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396161797/10000000000 : ℝ)|^2069 ≤ (44053908944707/100000000000000 : ℝ)^1557
        have hw : |(5396161797/10000000000 : ℝ)|=(5396161797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s5_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311737137/10000000000 : ℝ)*x 0 + (5396161789/10000000000 : ℝ)*x 1 + (-1064774471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311737137/10000000000 : ℝ)^2069 ≤ (2696274300139/6250000000000 : ℝ)^1557 := by
    have hnat : (5311737137 : ℕ)^2069*6250000000000^1557 ≤ 2696274300139^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311737137 10000000000 2696274300139 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396161789/10000000000 : ℝ)^2069 ≤ (22026954428959/50000000000000 : ℝ)^1557 := by
    have hnat : (5396161789 : ℕ)^2069*50000000000000^1557 ≤ 22026954428959^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396161789 10000000000 22026954428959 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064774471/5000000000 : ℝ)^2069 ≤ (6402851164141/50000000000000 : ℝ)^1557 := by
    have hnat : (1064774471 : ℕ)^2069*50000000000000^1557 ≤ 6402851164141^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064774471 5000000000 6402851164141 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311737137/10000000000 : ℝ), (5396161789/10000000000 : ℝ), (-1064774471/5000000000 : ℝ)] ![(2696274300139/6250000000000 : ℝ), (22026954428959/50000000000000 : ℝ), (6402851164141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311737137/10000000000 : ℝ)|^2069 ≤ (2696274300139/6250000000000 : ℝ)^1557
        have hw : |(5311737137/10000000000 : ℝ)|=(5311737137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396161789/10000000000 : ℝ)|^2069 ≤ (22026954428959/50000000000000 : ℝ)^1557
        have hw : |(5396161789/10000000000 : ℝ)|=(5396161789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064774471/5000000000 : ℝ)|^2069 ≤ (6402851164141/50000000000000 : ℝ)^1557
        have hw : |(-1064774471/5000000000 : ℝ)|=(1064774471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s5_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4372940383/10000000000 : ℝ)*x 0 + (1126516053/2500000000 : ℝ)*x 1 + (4243805977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372940383/10000000000 : ℝ)^2069 ≤ (1665775354979/5000000000000 : ℝ)^1557 := by
    have hnat : (4372940383 : ℕ)^2069*5000000000000^1557 ≤ 1665775354979^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372940383 10000000000 1665775354979 5000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126516053/2500000000 : ℝ)^2069 ≤ (8667482565807/25000000000000 : ℝ)^1557 := by
    have hnat : (1126516053 : ℕ)^2069*25000000000000^1557 ≤ 8667482565807^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126516053 2500000000 8667482565807 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243805977/10000000000 : ℝ)^2069 ≤ (32014562626027/100000000000000 : ℝ)^1557 := by
    have hnat : (4243805977 : ℕ)^2069*100000000000000^1557 ≤ 32014562626027^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243805977 10000000000 32014562626027 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372940383/10000000000 : ℝ), (1126516053/2500000000 : ℝ), (4243805977/10000000000 : ℝ)] ![(1665775354979/5000000000000 : ℝ), (8667482565807/25000000000000 : ℝ), (32014562626027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372940383/10000000000 : ℝ)|^2069 ≤ (1665775354979/5000000000000 : ℝ)^1557
        have hw : |(4372940383/10000000000 : ℝ)|=(4372940383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126516053/2500000000 : ℝ)|^2069 ≤ (8667482565807/25000000000000 : ℝ)^1557
        have hw : |(1126516053/2500000000 : ℝ)|=(1126516053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243805977/10000000000 : ℝ)|^2069 ≤ (32014562626027/100000000000000 : ℝ)^1557
        have hw : |(4243805977/10000000000 : ℝ)|=(4243805977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5529/50000 : ℝ) ^ (8275/2048 : ℝ) ≤ (6837842590954699/50000000000000000000 : ℝ) := by
    have hpowers : (5529/50000 : ℝ)^8275 ≤ (6837842590954699/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5529 : ℕ)^8275*50000000000000000000^2048 ≤ 6837842590954699^2048*50000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5529 50000 6837842590954699 50000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5529/50000 : ℝ)) (X := (6837842590954699/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (8275/2048 : ℝ) ≤ (7599131523644781/20000000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^8275 ≤ (7599131523644781/20000000000000000000 : ℝ)^2048 := by
      have hnat : (89 : ℕ)^8275*20000000000000000000^2048 ≤ 7599131523644781^2048*625^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 7599131523644781 20000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (7599131523644781/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006837842590954699/25000000000000000000 : ℝ) ≤ (10000676856106687/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (25006837842590954699/25000000000000000000 : ℝ)^2048 ≤ (10000676856106687/10000000000000000 : ℝ)^8275 := by
      have hnat : (25006837842590954699 : ℕ)^2048*10000000000000000^8275 ≤ 10000676856106687^8275*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006837842590954699 25000000000000000000 10000676856106687 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000676856106687/10000000000000000 : ℝ)) (X := (25006837842590954699/25000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051671342800133303/100000000000000000000 : ℝ) ≤ (10001278578159051/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (100051671342800133303/100000000000000000000 : ℝ)^2048 ≤ (10001278578159051/10000000000000000 : ℝ)^8275 := by
      have hnat : (100051671342800133303 : ℕ)^2048*10000000000000000^8275 ≤ 10001278578159051^8275*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051671342800133303 100000000000000000000 10001278578159051 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001278578159051/10000000000000000 : ℝ)) (X := (100051671342800133303/100000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007599131523644781/10000000000000000000 : ℝ) ≤ (2000376060042283/2000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (10007599131523644781/10000000000000000000 : ℝ)^2048 ≤ (2000376060042283/2000000000000000 : ℝ)^8275 := by
      have hnat : (10007599131523644781 : ℕ)^2048*2000000000000000^8275 ≤ 2000376060042283^8275*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007599131523644781 10000000000000000000 2000376060042283 2000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000376060042283/2000000000000000 : ℝ)) (X := (10007599131523644781/10000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6837842590954699/50000000000000000000 : ℝ) ≤ ((85969854246544313/86000000000000000 : ℝ)+2*(4065689543/2150000000000 : ℝ)*(5529/50000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (85969854246544313/86000000000000000 : ℝ)+2*(4065689543/2150000000000 : ℝ)*(5529/50000 : ℝ)=(10000676856106687/10000000000000000 : ℝ) by norm_num, show 1+2*(6837842590954699/50000000000000000000 : ℝ)=(25006837842590954699/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7599131523644781/20000000000000000000 : ℝ)+(6837842590954699/50000000000000000000 : ℝ) ≤ ((85969854246544313/86000000000000000 : ℝ)+(4065689543/2150000000000 : ℝ)*((89/625 : ℝ)+(5529/50000 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (85969854246544313/86000000000000000 : ℝ)+(4065689543/2150000000000 : ℝ)*((89/625 : ℝ)+(5529/50000 : ℝ))=(10001278578159051/10000000000000000 : ℝ) by norm_num, show 1+(7599131523644781/20000000000000000000 : ℝ)+(6837842590954699/50000000000000000000 : ℝ)=(100051671342800133303/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7599131523644781/20000000000000000000 : ℝ) ≤ ((85969854246544313/86000000000000000 : ℝ)+2*(4065689543/2150000000000 : ℝ)*(89/625 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (85969854246544313/86000000000000000 : ℝ)+2*(4065689543/2150000000000 : ℝ)*(89/625 : ℝ)=(2000376060042283/2000000000000000 : ℝ) by norm_num, show 1+2*(7599131523644781/20000000000000000000 : ℝ)=(10007599131523644781/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (85969854246544313/86000000000000000 : ℝ)*(X 1 0+X 2 0)+(4065689543/2150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (85969854246544313/86000000000000000 : ℝ)) (alpha := (4065689543/2150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (85969854246544313/86000000000000000 : ℝ)*(X 0 1+X 2 1)+(4065689543/2150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (85969854246544313/86000000000000000 : ℝ)) (alpha := (4065689543/2150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (85969854246544313/86000000000000000 : ℝ)*(X 0 2+X 1 2)+(4065689543/2150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (85969854246544313/86000000000000000 : ℝ)) (alpha := (4065689543/2150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2195211453/10000000000 : ℝ)*X 0 0+(134912789/250000000 : ℝ)*X 0 1+(2631224331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345549383/10000000000 : ℝ)*X 1 0+(-2263262289/10000000000 : ℝ)*X 1 1+(657806103/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672774771/5000000000 : ℝ)*X 2 0+(657806153/1250000000 : ℝ)*X 2 1+(-45265231/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186464897/5000000000 : ℝ)*X 0 0+(4243118609/10000000000 : ℝ)*X 0 1+(70417947/156250000 : ℝ)*X 0 2+(2186464897/5000000000 : ℝ)*X 1 0+(4243118609/10000000000 : ℝ)*X 1 1+(70417947/156250000 : ℝ)*X 1 2+(2186464897/5000000000 : ℝ)*X 2 0+(4243118609/10000000000 : ℝ)*X 2 1+(70417947/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548804207/2500000000 : ℝ)*X 0 0+(2631398647/5000000000 : ℝ)*X 0 1+(5396161793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311737129/10000000000 : ℝ)*X 1 0+(-1064774471/5000000000 : ℝ)*X 1 1+(5396161797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311737137/10000000000 : ℝ)*X 2 0+(5396161789/10000000000 : ℝ)*X 2 1+(-1064774471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372940383/10000000000 : ℝ)*X 0 0+(1126516053/2500000000 : ℝ)*X 0 1+(4243805977/10000000000 : ℝ)*X 0 2+(4372940383/10000000000 : ℝ)*X 1 0+(1126516053/2500000000 : ℝ)*X 1 1+(4243805977/10000000000 : ℝ)*X 1 2+(4372940383/10000000000 : ℝ)*X 2 0+(1126516053/2500000000 : ℝ)*X 2 1+(4243805977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145964423748154745751741/86000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231727903/100000000000000 : ℝ)*(base19) + (315336379/50000000000000 : ℝ)*(base23) + (338949/6250000000000 : ℝ)*(lower2) + (197039903/50000000000000 : ℝ)*(upper5) + (225049278641881/4000000000000 : ℝ)*(major0) + (225049278641881/4000000000000 : ℝ)*(major1) + (225049278641881/4000000000000 : ℝ)*(major2) + (7459209354225223/100000000000000 : ℝ)*(sp0) + (7459226370000403/100000000000000 : ℝ)*(sp1) + (7459255569485273/100000000000000 : ℝ)*(sp2) + (948301038203577/25000000000000 : ℝ)*(sp3) + (4684593281/10000000000000 : ℝ)*(sp4) + (14799214863/50000000000000 : ℝ)*(sp5) + (3522546337/100000000000000 : ℝ)*(sp7) + (758641535072129/20000000000000 : ℝ)*(f.failure) + (466203512509877/6250000000000 : ℝ)*(f.sum) + (17925997451/21500000000000000000000000 : ℝ)*base66 + (4654120535108753/344000000000000000000000000000 : ℝ)*base67 + (3395105842156753/344000000000000000000000000000 : ℝ)*base69 + (453892323851247/344000000000000000000000000000 : ℝ)*base72 + (46859252421/43000000000000000000000000 : ℝ)*base74 + (9350735276284753/344000000000000000000000000000 : ℝ)*base75 + (2778676720876753/344000000000000000000000000000 : ℝ)*base77 + (6428684393700753/344000000000000000000000000000 : ℝ)*base79 + (123631890221/43000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (9223159/1000000000000000000000 : ℝ)*base90 + (9223159/1000000000000000000000 : ℝ)*base92 + (9223159/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14597594518097227759392189/2150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1223454643/100000000000000 : ℝ)*(base19) + (336166169/25000000000000 : ℝ)*(base23) + (13383993/10000000000000 : ℝ)*(upper3) + (4998609/10000000000000 : ℝ)*(lower4) + (69059263/50000000000000 : ℝ)*(upper5) + (5655640925135751/100000000000000 : ℝ)*(major0) + (5655640925135751/100000000000000 : ℝ)*(major1) + (5655640925135751/100000000000000 : ℝ)*(major2) + (32339277013/100000000000000 : ℝ)*(sp1) + (1392924089/4000000000000 : ℝ)*(sp2) + (7498246417481397/100000000000000 : ℝ)*(sp4) + (7498212854749741/100000000000000 : ℝ)*(sp5) + (1499642049942899/20000000000000 : ℝ)*(sp6) + (953258801617699/25000000000000 : ℝ)*(sp7) + (953258801617699/25000000000000 : ℝ)*(f.failure) + (7498246417481397/100000000000000 : ℝ)*(f.sum) + (371971490453/107500000000000000000000000 : ℝ)*base65 + (102296477008245937/8600000000000000000000000000000 : ℝ)*base68 + (80217869378045937/8600000000000000000000000000000 : ℝ)*base70 + (80591733884154063/8600000000000000000000000000000 : ℝ)*base71 + (619750380609/215000000000000000000000000 : ℝ)*base74 + (395599326602845937/8600000000000000000000000000000 : ℝ)*base76 + (3908126810045937/8600000000000000000000000000000 : ℝ)*base78 + (75425048046445937/8600000000000000000000000000000 : ℝ)*base80 + (303373448297/107500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9118629/1250000000000000000000 : ℝ)*base90 + (9118629/1250000000000000000000 : ℝ)*base92 + (9118629/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1083_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1083_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3337/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1759/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1083_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1083_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1083_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3337/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1759/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1083_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
