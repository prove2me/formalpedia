-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1052_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:56:34.75533+00:00
-- url     : https://prove2.me/submissions/67bd9713-25a2-4d00-90d9-486e89aa4339

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
theorem support_rectangle_w1052_s3_0 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205748963/10000000000 : ℝ)*x 0 + (1359797283/2500000000 : ℝ)*x 1 + (5222827711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205748963/10000000000 : ℝ)^8245 ≤ (6692415047991/50000000000000 : ℝ)^6197 := by
    have hnat : (2205748963 : ℕ)^8245*50000000000000^6197 ≤ 6692415047991^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205748963 10000000000 6692415047991 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359797283/2500000000 : ℝ)^8245 ≤ (44476728063167/100000000000000 : ℝ)^6197 := by
    have hnat : (1359797283 : ℕ)^8245*100000000000000^6197 ≤ 44476728063167^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359797283 2500000000 44476728063167 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5222827711/10000000000 : ℝ)^8245 ≤ (42138441830679/100000000000000 : ℝ)^6197 := by
    have hnat : (5222827711 : ℕ)^8245*100000000000000^6197 ≤ 42138441830679^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222827711 10000000000 42138441830679 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205748963/10000000000 : ℝ), (1359797283/2500000000 : ℝ), (5222827711/10000000000 : ℝ)] ![(6692415047991/50000000000000 : ℝ), (44476728063167/100000000000000 : ℝ), (42138441830679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205748963/10000000000 : ℝ)|^8245 ≤ (6692415047991/50000000000000 : ℝ)^6197
        have hw : |(-2205748963/10000000000 : ℝ)|=(2205748963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359797283/2500000000 : ℝ)|^8245 ≤ (44476728063167/100000000000000 : ℝ)^6197
        have hw : |(1359797283/2500000000 : ℝ)|=(1359797283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5222827711/10000000000 : ℝ)|^8245 ≤ (42138441830679/100000000000000 : ℝ)^6197
        have hw : |(5222827711/10000000000 : ℝ)|=(5222827711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s3_1 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356054183/10000000000 : ℝ)*x 0 + (-579145701/2500000000 : ℝ)*x 1 + (81606681/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356054183/10000000000 : ℝ)^8245 ≤ (8714911171243/20000000000000 : ℝ)^6197 := by
    have hnat : (5356054183 : ℕ)^8245*20000000000000^6197 ≤ 8714911171243^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356054183 10000000000 8714911171243 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579145701/2500000000 : ℝ)^8245 ≤ (571480146459/4000000000000 : ℝ)^6197 := by
    have hnat : (579145701 : ℕ)^8245*4000000000000^6197 ≤ 571480146459^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579145701 2500000000 571480146459 4000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81606681/156250000 : ℝ)^8245 ≤ (42138440467397/100000000000000 : ℝ)^6197 := by
    have hnat : (81606681 : ℕ)^8245*100000000000000^6197 ≤ 42138440467397^6197*156250000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81606681 156250000 42138440467397 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356054183/10000000000 : ℝ), (-579145701/2500000000 : ℝ), (81606681/156250000 : ℝ)] ![(8714911171243/20000000000000 : ℝ), (571480146459/4000000000000 : ℝ), (42138440467397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356054183/10000000000 : ℝ)|^8245 ≤ (8714911171243/20000000000000 : ℝ)^6197
        have hw : |(5356054183/10000000000 : ℝ)|=(5356054183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579145701/2500000000 : ℝ)|^8245 ≤ (571480146459/4000000000000 : ℝ)^6197
        have hw : |(-579145701/2500000000 : ℝ)|=(579145701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81606681/156250000 : ℝ)|^8245 ≤ (42138440467397/100000000000000 : ℝ)^6197
        have hw : |(81606681/156250000 : ℝ)|=(81606681/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s3_2 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1339013523/2500000000 : ℝ)*x 0 + (652853429/1250000000 : ℝ)*x 1 + (-579145781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339013523/2500000000 : ℝ)^8245 ≤ (4357455487121/10000000000000 : ℝ)^6197 := by
    have hnat : (1339013523 : ℕ)^8245*10000000000000^6197 ≤ 4357455487121^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339013523 2500000000 4357455487121 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652853429/1250000000 : ℝ)^8245 ≤ (5267304854469/12500000000000 : ℝ)^6197 := by
    have hnat : (652853429 : ℕ)^8245*12500000000000^6197 ≤ 5267304854469^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652853429 1250000000 5267304854469 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579145781/2500000000 : ℝ)^8245 ≤ (714350314361/5000000000000 : ℝ)^6197 := by
    have hnat : (579145781 : ℕ)^8245*5000000000000^6197 ≤ 714350314361^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579145781 2500000000 714350314361 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339013523/2500000000 : ℝ), (652853429/1250000000 : ℝ), (-579145781/2500000000 : ℝ)] ![(4357455487121/10000000000000 : ℝ), (5267304854469/12500000000000 : ℝ), (714350314361/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339013523/2500000000 : ℝ)|^8245 ≤ (4357455487121/10000000000000 : ℝ)^6197
        have hw : |(1339013523/2500000000 : ℝ)|=(1339013523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652853429/1250000000 : ℝ)|^8245 ≤ (5267304854469/12500000000000 : ℝ)^6197
        have hw : |(652853429/1250000000 : ℝ)|=(652853429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579145781/2500000000 : ℝ)|^8245 ≤ (714350314361/5000000000000 : ℝ)^6197
        have hw : |(-579145781/2500000000 : ℝ)|=(579145781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s3_3 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874918657/2000000000 : ℝ)*x 0 + (4168347967/10000000000 : ℝ)*x 1 + (1147802289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874918657/2000000000 : ℝ)^8245 ≤ (1664346997361/5000000000000 : ℝ)^6197 := by
    have hnat : (874918657 : ℕ)^8245*5000000000000^6197 ≤ 1664346997361^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874918657 2000000000 1664346997361 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168347967/10000000000 : ℝ)^8245 ≤ (31215386069993/100000000000000 : ℝ)^6197 := by
    have hnat : (4168347967 : ℕ)^8245*100000000000000^6197 ≤ 31215386069993^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168347967 10000000000 31215386069993 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147802289/2500000000 : ℝ)^8245 ≤ (17748836980943/50000000000000 : ℝ)^6197 := by
    have hnat : (1147802289 : ℕ)^8245*50000000000000^6197 ≤ 17748836980943^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147802289 2500000000 17748836980943 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874918657/2000000000 : ℝ), (4168347967/10000000000 : ℝ), (1147802289/2500000000 : ℝ)] ![(1664346997361/5000000000000 : ℝ), (31215386069993/100000000000000 : ℝ), (17748836980943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874918657/2000000000 : ℝ)|^8245 ≤ (1664346997361/5000000000000 : ℝ)^6197
        have hw : |(874918657/2000000000 : ℝ)|=(874918657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168347967/10000000000 : ℝ)|^8245 ≤ (31215386069993/100000000000000 : ℝ)^6197
        have hw : |(4168347967/10000000000 : ℝ)|=(4168347967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147802289/2500000000 : ℝ)|^8245 ≤ (17748836980943/50000000000000 : ℝ)^6197
        have hw : |(1147802289/2500000000 : ℝ)|=(1147802289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s3_4 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-275721523/1250000000 : ℝ)*x 0 + (5223723741/10000000000 : ℝ)*x 1 + (5438287759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275721523/1250000000 : ℝ)^8245 ≤ (6692508786409/50000000000000 : ℝ)^6197 := by
    have hnat : (275721523 : ℕ)^8245*50000000000000^6197 ≤ 6692508786409^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275721523 1250000000 6692508786409 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5223723741/10000000000 : ℝ)^8245 ≤ (842961210799/2000000000000 : ℝ)^6197 := by
    have hnat : (5223723741 : ℕ)^8245*2000000000000^6197 ≤ 842961210799^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223723741 10000000000 842961210799 2000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438287759/10000000000 : ℝ)^8245 ≤ (44466921869049/100000000000000 : ℝ)^6197 := by
    have hnat : (5438287759 : ℕ)^8245*100000000000000^6197 ≤ 44466921869049^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438287759 10000000000 44466921869049 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275721523/1250000000 : ℝ), (5223723741/10000000000 : ℝ), (5438287759/10000000000 : ℝ)] ![(6692508786409/50000000000000 : ℝ), (842961210799/2000000000000 : ℝ), (44466921869049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275721523/1250000000 : ℝ)|^8245 ≤ (6692508786409/50000000000000 : ℝ)^6197
        have hw : |(-275721523/1250000000 : ℝ)|=(275721523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5223723741/10000000000 : ℝ)|^8245 ≤ (842961210799/2000000000000 : ℝ)^6197
        have hw : |(5223723741/10000000000 : ℝ)|=(5223723741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438287759/10000000000 : ℝ)|^8245 ≤ (44466921869049/100000000000000 : ℝ)^6197
        have hw : |(5438287759/10000000000 : ℝ)|=(5438287759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s3_5 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325403289/2500000000 : ℝ)*x 0 + (-2101121981/10000000000 : ℝ)*x 1 + (1087657627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325403289/2500000000 : ℝ)^8245 ≤ (42986265441961/100000000000000 : ℝ)^6197 := by
    have hnat : (1325403289 : ℕ)^8245*100000000000000^6197 ≤ 42986265441961^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325403289 2500000000 42986265441961 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101121981/10000000000 : ℝ)^8245 ≤ (627340429363/5000000000000 : ℝ)^6197 := by
    have hnat : (2101121981 : ℕ)^8245*5000000000000^6197 ≤ 627340429363^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101121981 10000000000 627340429363 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087657627/2000000000 : ℝ)^8245 ≤ (22233462979753/50000000000000 : ℝ)^6197 := by
    have hnat : (1087657627 : ℕ)^8245*50000000000000^6197 ≤ 22233462979753^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087657627 2000000000 22233462979753 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325403289/2500000000 : ℝ), (-2101121981/10000000000 : ℝ), (1087657627/2000000000 : ℝ)] ![(42986265441961/100000000000000 : ℝ), (627340429363/5000000000000 : ℝ), (22233462979753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325403289/2500000000 : ℝ)|^8245 ≤ (42986265441961/100000000000000 : ℝ)^6197
        have hw : |(1325403289/2500000000 : ℝ)|=(1325403289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101121981/10000000000 : ℝ)|^8245 ≤ (627340429363/5000000000000 : ℝ)^6197
        have hw : |(-2101121981/10000000000 : ℝ)|=(2101121981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087657627/2000000000 : ℝ)|^8245 ≤ (22233462979753/50000000000000 : ℝ)^6197
        have hw : |(1087657627/2000000000 : ℝ)|=(1087657627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s3_6 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301612879/10000000000 : ℝ)*x 0 + (5438288061/10000000000 : ℝ)*x 1 + (-1050561229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301612879/10000000000 : ℝ)^8245 ≤ (8597252490751/20000000000000 : ℝ)^6197 := by
    have hnat : (5301612879 : ℕ)^8245*20000000000000^6197 ≤ 8597252490751^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301612879 10000000000 8597252490751 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438288061/10000000000 : ℝ)^8245 ≤ (4446692515447/10000000000000 : ℝ)^6197 := by
    have hnat : (5438288061 : ℕ)^8245*10000000000000^6197 ≤ 4446692515447^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438288061 10000000000 4446692515447 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050561229/5000000000 : ℝ)^8245 ≤ (12546812377001/100000000000000 : ℝ)^6197 := by
    have hnat : (1050561229 : ℕ)^8245*100000000000000^6197 ≤ 12546812377001^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050561229 5000000000 12546812377001 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301612879/10000000000 : ℝ), (5438288061/10000000000 : ℝ), (-1050561229/5000000000 : ℝ)] ![(8597252490751/20000000000000 : ℝ), (4446692515447/10000000000000 : ℝ), (12546812377001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301612879/10000000000 : ℝ)|^8245 ≤ (8597252490751/20000000000000 : ℝ)^6197
        have hw : |(5301612879/10000000000 : ℝ)|=(5301612879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438288061/10000000000 : ℝ)|^8245 ≤ (4446692515447/10000000000000 : ℝ)^6197
        have hw : |(5438288061/10000000000 : ℝ)|=(5438288061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050561229/5000000000 : ℝ)|^8245 ≤ (12546812377001/100000000000000 : ℝ)^6197
        have hw : |(-1050561229/5000000000 : ℝ)|=(1050561229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s3_7 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187319333/5000000000 : ℝ)*x 0 + (229472901/500000000 : ℝ)*x 1 + (166804383/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187319333/5000000000 : ℝ)^8245 ≤ (33287399378077/100000000000000 : ℝ)^6197 := by
    have hnat : (2187319333 : ℕ)^8245*100000000000000^6197 ≤ 33287399378077^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187319333 5000000000 33287399378077 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229472901/500000000 : ℝ)^8245 ≤ (2217478840097/6250000000000 : ℝ)^6197 := by
    have hnat : (229472901 : ℕ)^8245*6250000000000^6197 ≤ 2217478840097^6197*500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229472901 500000000 2217478840097 6250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166804383/400000000 : ℝ)^8245 ≤ (3904117394631/12500000000000 : ℝ)^6197 := by
    have hnat : (166804383 : ℕ)^8245*12500000000000^6197 ≤ 3904117394631^6197*400000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166804383 400000000 3904117394631 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187319333/5000000000 : ℝ), (229472901/500000000 : ℝ), (166804383/400000000 : ℝ)] ![(33287399378077/100000000000000 : ℝ), (2217478840097/6250000000000 : ℝ), (3904117394631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187319333/5000000000 : ℝ)|^8245 ≤ (33287399378077/100000000000000 : ℝ)^6197
        have hw : |(2187319333/5000000000 : ℝ)|=(2187319333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229472901/500000000 : ℝ)|^8245 ≤ (2217478840097/6250000000000 : ℝ)^6197
        have hw : |(229472901/500000000 : ℝ)|=(229472901/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166804383/400000000 : ℝ)|^8245 ≤ (3904117394631/12500000000000 : ℝ)^6197
        have hw : |(166804383/400000000 : ℝ)|=(166804383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1052_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10349/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7463/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4321/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4321/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4321/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4321/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4321/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4321/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4321/50000 : ℝ) ^ (2061/512 : ℝ) ≤ (131037931245303/2500000000000000000 : ℝ) := by
    have hpowers : (4321/50000 : ℝ)^2061 ≤ (131037931245303/2500000000000000000 : ℝ)^512 := by
      have hnat : (4321 : ℕ)^2061*2500000000000000000^512 ≤ 131037931245303^512*50000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4321 50000 131037931245303 2500000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4321/50000 : ℝ)) (X := (131037931245303/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16787/100000 : ℝ) ^ (2061/512 : ℝ) ≤ (75895136096644981/100000000000000000000 : ℝ) := by
    have hpowers : (16787/100000 : ℝ)^2061 ≤ (75895136096644981/100000000000000000000 : ℝ)^512 := by
      have hnat : (16787 : ℕ)^2061*100000000000000000000^512 ≤ 75895136096644981^512*100000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16787 100000 75895136096644981 100000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16787/100000 : ℝ)) (X := (75895136096644981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250131037931245303/1250000000000000000 : ℝ) ≤ (2500065103132419/2500000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (1250131037931245303/1250000000000000000 : ℝ)^512 ≤ (2500065103132419/2500000000000000 : ℝ)^2061 := by
      have hnat : (1250131037931245303 : ℕ)^512*2500000000000000^2061 ≤ 2500065103132419^2061*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250131037931245303 1250000000000000000 2500065103132419 2500000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500065103132419/2500000000000000 : ℝ)) (X := (1250131037931245303/1250000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100081136653346457101/100000000000000000000 : ℝ) ≤ (5001007503791229/5000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (100081136653346457101/100000000000000000000 : ℝ)^512 ≤ (5001007503791229/5000000000000000 : ℝ)^2061 := by
      have hnat : (100081136653346457101 : ℕ)^512*5000000000000000^2061 ≤ 5001007503791229^2061*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100081136653346457101 100000000000000000000 5001007503791229 5000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001007503791229/5000000000000000 : ℝ)) (X := (100081136653346457101/100000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50075895136096644981/50000000000000000000 : ℝ) ≤ (250094240065881/250000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (50075895136096644981/50000000000000000000 : ℝ)^512 ≤ (250094240065881/250000000000000 : ℝ)^2061 := by
      have hnat : (50075895136096644981 : ℕ)^512*250000000000000^2061 ≤ 250094240065881^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075895136096644981 50000000000000000000 250094240065881 250000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250094240065881/250000000000000 : ℝ)) (X := (50075895136096644981/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(131037931245303/2500000000000000000 : ℝ) ≤ ((6785149553263493911/6787500000000000000 : ℝ)+2*(292432508797/135750000000000 : ℝ)*(4321/50000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (6785149553263493911/6787500000000000000 : ℝ)+2*(292432508797/135750000000000 : ℝ)*(4321/50000 : ℝ)=(2500065103132419/2500000000000000 : ℝ) by norm_num, show 1+2*(131037931245303/2500000000000000000 : ℝ)=(1250131037931245303/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75895136096644981/100000000000000000000 : ℝ)+(131037931245303/2500000000000000000 : ℝ) ≤ ((6785149553263493911/6787500000000000000 : ℝ)+(292432508797/135750000000000 : ℝ)*((16787/100000 : ℝ)+(4321/50000 : ℝ)))^(2061/512 : ℝ) := by
    rw [show (6785149553263493911/6787500000000000000 : ℝ)+(292432508797/135750000000000 : ℝ)*((16787/100000 : ℝ)+(4321/50000 : ℝ))=(5001007503791229/5000000000000000 : ℝ) by norm_num, show 1+(75895136096644981/100000000000000000000 : ℝ)+(131037931245303/2500000000000000000 : ℝ)=(100081136653346457101/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75895136096644981/100000000000000000000 : ℝ) ≤ ((6785149553263493911/6787500000000000000 : ℝ)+2*(292432508797/135750000000000 : ℝ)*(16787/100000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (6785149553263493911/6787500000000000000 : ℝ)+2*(292432508797/135750000000000 : ℝ)*(16787/100000 : ℝ)=(250094240065881/250000000000000 : ℝ) by norm_num, show 1+2*(75895136096644981/100000000000000000000 : ℝ)=(50075895136096644981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6785149553263493911/6787500000000000000 : ℝ)*(X 1 0+X 2 0)+(292432508797/135750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (4321/50000 : ℝ)) (hi := (16787/100000 : ℝ)) (c := (6785149553263493911/6787500000000000000 : ℝ)) (alpha := (292432508797/135750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6785149553263493911/6787500000000000000 : ℝ)*(X 0 1+X 2 1)+(292432508797/135750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (4321/50000 : ℝ)) (hi := (16787/100000 : ℝ)) (c := (6785149553263493911/6787500000000000000 : ℝ)) (alpha := (292432508797/135750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6785149553263493911/6787500000000000000 : ℝ)*(X 0 2+X 1 2)+(292432508797/135750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (4321/50000 : ℝ)) (hi := (16787/100000 : ℝ)) (c := (6785149553263493911/6787500000000000000 : ℝ)) (alpha := (292432508797/135750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2205748963/10000000000 : ℝ)*X 0 0+(1359797283/2500000000 : ℝ)*X 0 1+(5222827711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356054183/10000000000 : ℝ)*X 1 0+(-579145701/2500000000 : ℝ)*X 1 1+(81606681/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339013523/2500000000 : ℝ)*X 2 0+(652853429/1250000000 : ℝ)*X 2 1+(-579145781/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874918657/2000000000 : ℝ)*X 0 0+(4168347967/10000000000 : ℝ)*X 0 1+(1147802289/2500000000 : ℝ)*X 0 2+(874918657/2000000000 : ℝ)*X 1 0+(4168347967/10000000000 : ℝ)*X 1 1+(1147802289/2500000000 : ℝ)*X 1 2+(874918657/2000000000 : ℝ)*X 2 0+(4168347967/10000000000 : ℝ)*X 2 1+(1147802289/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-275721523/1250000000 : ℝ)*X 0 0+(5223723741/10000000000 : ℝ)*X 0 1+(5438287759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325403289/2500000000 : ℝ)*X 1 0+(-2101121981/10000000000 : ℝ)*X 1 1+(1087657627/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301612879/10000000000 : ℝ)*X 2 0+(5438288061/10000000000 : ℝ)*X 2 1+(-1050561229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187319333/5000000000 : ℝ)*X 0 0+(229472901/500000000 : ℝ)*X 0 1+(166804383/400000000 : ℝ)*X 0 2+(2187319333/5000000000 : ℝ)*X 1 0+(229472901/500000000 : ℝ)*X 1 1+(166804383/400000000 : ℝ)*X 1 2+(2187319333/5000000000 : ℝ)*X 2 0+(229472901/500000000 : ℝ)*X 2 1+(166804383/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (312978283952667522349845519/56562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1114243879/100000000000000 : ℝ)*(base19) + (1072263413/100000000000000 : ℝ)*(base23) + (10911857/50000000000000 : ℝ)*(upper2) + (280959773/100000000000000 : ℝ)*(upper3) + (3493392832328871/100000000000000 : ℝ)*(major0) + (3493392832328871/100000000000000 : ℝ)*(major1) + (3493392832328871/100000000000000 : ℝ)*(major2) + (4621914152964217/100000000000000 : ℝ)*(sp0) + (924384395874329/20000000000000 : ℝ)*(sp1) + (1155480402052773/25000000000000 : ℝ)*(sp2) + (591212674881337/25000000000000 : ℝ)*(sp3) + (8940651307/100000000000000 : ℝ)*(sp4) + (413141019/100000000000000 : ℝ)*(sp6) + (11687072939/100000000000000 : ℝ)*(sp7) + (147803899162393/6250000000000 : ℝ)*(f.failure) + (1155480773403881/25000000000000 : ℝ)*(f.sum) + (9076127805583/4525000000000000000000000000 : ℝ)*base65 + (375474121597034827/226250000000000000000000000000000 : ℝ)*base67 + (1492880317139534827/226250000000000000000000000000000 : ℝ)*base69 + (282410446194534827/226250000000000000000000000000000 : ℝ)*base71 + (3689514135279/2262500000000000000000000000 : ℝ)*base73 + (1309846922414534827/226250000000000000000000000000000 : ℝ)*base75 + (2914573278032034827/226250000000000000000000000000000 : ℝ)*base77 + (34373403067965173/226250000000000000000000000000000 : ℝ)*base80 + (8246545105617/4525000000000000000000000000 : ℝ)*base82 + (4301519/312500000000000000000 : ℝ)*base89 + (4301519/312500000000000000000 : ℝ)*base91 + (4301519/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97328959940078835708381009/56562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724961703/100000000000000 : ℝ)*(base19) + (251009023/50000000000000 : ℝ)*(base23) + (25505261/50000000000000 : ℝ)*(upper2) + (115890513/100000000000000 : ℝ)*(upper3) + (1761315706230927/50000000000000 : ℝ)*(major0) + (1761315706230927/50000000000000 : ℝ)*(major1) + (1761315706230927/50000000000000 : ℝ)*(major2) + (18103312009/100000000000000 : ℝ)*(sp1) + (10736070961/100000000000000 : ℝ)*(sp2) + (72799979/4000000000000 : ℝ)*(sp3) + (582575904942449/12500000000000 : ℝ)*(sp4) + (116514710281647/2500000000000 : ℝ)*(sp5) + (932119200290117/20000000000000 : ℝ)*(sp6) + (149040856751679/6250000000000 : ℝ)*(sp7) + (119232776401317/5000000000000 : ℝ)*(f.failure) + (582575904942449/12500000000000 : ℝ)*(f.sum) + (11068324963183/4525000000000000000000000000 : ℝ)*base66 + (1689323208086153499/113125000000000000000000000000000 : ℝ)*base67 + (2444392994879278499/113125000000000000000000000000000 : ℝ)*base69 + (1492799126668028499/113125000000000000000000000000000 : ℝ)*base71 + (2284509074633/4525000000000000000000000000 : ℝ)*base74 + (868727390649278499/113125000000000000000000000000000 : ℝ)*base75 + (723095981855528499/113125000000000000000000000000000 : ℝ)*base77 + (1524555043170528499/113125000000000000000000000000000 : ℝ)*base79 + (9037070715471/2262500000000000000000000000 : ℝ)*base81 + (324411/250000000000000000000 : ℝ)*base89 + (324411/250000000000000000000 : ℝ)*base91 + (324411/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1052_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7463/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1052_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1052_s4_0 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209565021/10000000000 : ℝ)*x 0 + (2703298417/5000000000 : ℝ)*x 1 + (1050585571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209565021/10000000000 : ℝ)^8245 ≤ (2683129626967/20000000000000 : ℝ)^6197 := by
    have hnat : (2209565021 : ℕ)^8245*20000000000000^6197 ≤ 2683129626967^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209565021 10000000000 2683129626967 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703298417/5000000000 : ℝ)^8245 ≤ (44122492620681/100000000000000 : ℝ)^6197 := by
    have hnat : (2703298417 : ℕ)^8245*100000000000000^6197 ≤ 44122492620681^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703298417 5000000000 44122492620681 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050585571/2000000000 : ℝ)^8245 ≤ (2653866201327/6250000000000 : ℝ)^6197 := by
    have hnat : (1050585571 : ℕ)^8245*6250000000000^6197 ≤ 2653866201327^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050585571 2000000000 2653866201327 6250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209565021/10000000000 : ℝ), (2703298417/5000000000 : ℝ), (1050585571/2000000000 : ℝ)] ![(2683129626967/20000000000000 : ℝ), (44122492620681/100000000000000 : ℝ), (2653866201327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209565021/10000000000 : ℝ)|^8245 ≤ (2683129626967/20000000000000 : ℝ)^6197
        have hw : |(-2209565021/10000000000 : ℝ)|=(2209565021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703298417/5000000000 : ℝ)|^8245 ≤ (44122492620681/100000000000000 : ℝ)^6197
        have hw : |(2703298417/5000000000 : ℝ)|=(2703298417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050585571/2000000000 : ℝ)|^8245 ≤ (2653866201327/6250000000000 : ℝ)^6197
        have hw : |(1050585571/2000000000 : ℝ)|=(1050585571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s4_1 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668499197/1250000000 : ℝ)*x 0 + (-35745917/156250000 : ℝ)*x 1 + (5252927867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668499197/1250000000 : ℝ)^8245 ≤ (43487327664707/100000000000000 : ℝ)^6197 := by
    have hnat : (668499197 : ℕ)^8245*100000000000000^6197 ≤ 43487327664707^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668499197 1250000000 43487327664707 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35745917/156250000 : ℝ)^8245 ≤ (14050812975609/100000000000000 : ℝ)^6197 := by
    have hnat : (35745917 : ℕ)^8245*100000000000000^6197 ≤ 14050812975609^6197*156250000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35745917 156250000 14050812975609 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252927867/10000000000 : ℝ)^8245 ≤ (4246185935029/10000000000000 : ℝ)^6197 := by
    have hnat : (5252927867 : ℕ)^8245*10000000000000^6197 ≤ 4246185935029^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252927867 10000000000 4246185935029 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668499197/1250000000 : ℝ), (-35745917/156250000 : ℝ), (5252927867/10000000000 : ℝ)] ![(43487327664707/100000000000000 : ℝ), (14050812975609/100000000000000 : ℝ), (4246185935029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668499197/1250000000 : ℝ)|^8245 ≤ (43487327664707/100000000000000 : ℝ)^6197
        have hw : |(668499197/1250000000 : ℝ)|=(668499197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35745917/156250000 : ℝ)|^8245 ≤ (14050812975609/100000000000000 : ℝ)^6197
        have hw : |(-35745917/156250000 : ℝ)|=(35745917/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252927867/10000000000 : ℝ)|^8245 ≤ (4246185935029/10000000000000 : ℝ)^6197
        have hw : |(5252927867/10000000000 : ℝ)|=(5252927867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s4_2 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347993579/10000000000 : ℝ)*x 0 + (5252927873/10000000000 : ℝ)*x 1 + (-571934669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347993579/10000000000 : ℝ)^8245 ≤ (10871831924291/25000000000000 : ℝ)^6197 := by
    have hnat : (5347993579 : ℕ)^8245*25000000000000^6197 ≤ 10871831924291^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347993579 10000000000 10871831924291 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252927873/10000000000 : ℝ)^8245 ≤ (2123092970741/5000000000000 : ℝ)^6197 := by
    have hnat : (5252927873 : ℕ)^8245*5000000000000^6197 ≤ 2123092970741^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252927873 10000000000 2123092970741 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571934669/2500000000 : ℝ)^8245 ≤ (14050812877551/100000000000000 : ℝ)^6197 := by
    have hnat : (571934669 : ℕ)^8245*100000000000000^6197 ≤ 14050812877551^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571934669 2500000000 14050812877551 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347993579/10000000000 : ℝ), (5252927873/10000000000 : ℝ), (-571934669/2500000000 : ℝ)] ![(10871831924291/25000000000000 : ℝ), (2123092970741/5000000000000 : ℝ), (14050812877551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347993579/10000000000 : ℝ)|^8245 ≤ (10871831924291/25000000000000 : ℝ)^6197
        have hw : |(5347993579/10000000000 : ℝ)|=(5347993579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252927873/10000000000 : ℝ)|^8245 ≤ (2123092970741/5000000000000 : ℝ)^6197
        have hw : |(5252927873/10000000000 : ℝ)|=(5252927873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571934669/2500000000 : ℝ)|^8245 ≤ (14050812877551/100000000000000 : ℝ)^6197
        have hw : |(-571934669/2500000000 : ℝ)|=(571934669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s4_3 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376862857/10000000000 : ℝ)*x 0 + (1057328413/2500000000 : ℝ)*x 1 + (1132411659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376862857/10000000000 : ℝ)^8245 ≤ (6661983740973/20000000000000 : ℝ)^6197 := by
    have hnat : (4376862857 : ℕ)^8245*20000000000000^6197 ≤ 6661983740973^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376862857 10000000000 6661983740973 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057328413/2500000000 : ℝ)^8245 ≤ (6364856745701/20000000000000 : ℝ)^6197 := by
    have hnat : (1057328413 : ℕ)^8245*20000000000000^6197 ≤ 6364856745701^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057328413 2500000000 6364856745701 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132411659/2500000000 : ℝ)^8245 ≤ (17432898775909/50000000000000 : ℝ)^6197 := by
    have hnat : (1132411659 : ℕ)^8245*50000000000000^6197 ≤ 17432898775909^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132411659 2500000000 17432898775909 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376862857/10000000000 : ℝ), (1057328413/2500000000 : ℝ), (1132411659/2500000000 : ℝ)] ![(6661983740973/20000000000000 : ℝ), (6364856745701/20000000000000 : ℝ), (17432898775909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376862857/10000000000 : ℝ)|^8245 ≤ (6661983740973/20000000000000 : ℝ)^6197
        have hw : |(4376862857/10000000000 : ℝ)|=(4376862857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057328413/2500000000 : ℝ)|^8245 ≤ (6364856745701/20000000000000 : ℝ)^6197
        have hw : |(1057328413/2500000000 : ℝ)|=(1057328413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132411659/2500000000 : ℝ)|^8245 ≤ (17432898775909/50000000000000 : ℝ)^6197
        have hw : |(1132411659/2500000000 : ℝ)|=(1132411659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s4_4 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209573399/10000000000 : ℝ)*x 0 + (3283363/6250000 : ℝ)*x 1 + (5406141939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209573399/10000000000 : ℝ)^8245 ≤ (13415715813949/100000000000000 : ℝ)^6197 := by
    have hnat : (2209573399 : ℕ)^8245*100000000000000^6197 ≤ 13415715813949^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209573399 10000000000 13415715813949 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3283363/6250000 : ℝ)^8245 ≤ (21233365336413/50000000000000 : ℝ)^6197 := by
    have hnat : (3283363 : ℕ)^8245*50000000000000^6197 ≤ 21233365336413^6197*6250000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3283363 6250000 21233365336413 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406141939/10000000000 : ℝ)^8245 ≤ (22058776745993/50000000000000 : ℝ)^6197 := by
    have hnat : (5406141939 : ℕ)^8245*50000000000000^6197 ≤ 22058776745993^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406141939 10000000000 22058776745993 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209573399/10000000000 : ℝ), (3283363/6250000 : ℝ), (5406141939/10000000000 : ℝ)] ![(13415715813949/100000000000000 : ℝ), (21233365336413/50000000000000 : ℝ), (22058776745993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209573399/10000000000 : ℝ)|^8245 ≤ (13415715813949/100000000000000 : ℝ)^6197
        have hw : |(-2209573399/10000000000 : ℝ)|=(2209573399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3283363/6250000 : ℝ)|^8245 ≤ (21233365336413/50000000000000 : ℝ)^6197
        have hw : |(3283363/6250000 : ℝ)|=(3283363/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406141939/10000000000 : ℝ)|^8245 ≤ (22058776745993/50000000000000 : ℝ)^6197
        have hw : |(5406141939/10000000000 : ℝ)|=(5406141939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s4_5 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327333139/2500000000 : ℝ)*x 0 + (-533631153/2500000000 : ℝ)*x 1 + (675767749/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327333139/2500000000 : ℝ)^8245 ≤ (43069560423183/100000000000000 : ℝ)^6197 := by
    have hnat : (1327333139 : ℕ)^8245*100000000000000^6197 ≤ 43069560423183^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327333139 2500000000 43069560423183 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533631153/2500000000 : ℝ)^8245 ≤ (1601610687991/12500000000000 : ℝ)^6197 := by
    have hnat : (533631153 : ℕ)^8245*12500000000000^6197 ≤ 1601610687991^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533631153 2500000000 1601610687991 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675767749/1250000000 : ℝ)^8245 ≤ (22058777033719/50000000000000 : ℝ)^6197 := by
    have hnat : (675767749 : ℕ)^8245*50000000000000^6197 ≤ 22058777033719^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675767749 1250000000 22058777033719 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327333139/2500000000 : ℝ), (-533631153/2500000000 : ℝ), (675767749/1250000000 : ℝ)] ![(43069560423183/100000000000000 : ℝ), (1601610687991/12500000000000 : ℝ), (22058777033719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327333139/2500000000 : ℝ)|^8245 ≤ (43069560423183/100000000000000 : ℝ)^6197
        have hw : |(1327333139/2500000000 : ℝ)|=(1327333139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533631153/2500000000 : ℝ)|^8245 ≤ (1601610687991/12500000000000 : ℝ)^6197
        have hw : |(-533631153/2500000000 : ℝ)|=(533631153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675767749/1250000000 : ℝ)|^8245 ≤ (22058777033719/50000000000000 : ℝ)^6197
        have hw : |(675767749/1250000000 : ℝ)|=(675767749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s4_6 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309332579/10000000000 : ℝ)*x 0 + (5406141969/10000000000 : ℝ)*x 1 + (-213452461/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309332579/10000000000 : ℝ)^8245 ≤ (2153478033571/5000000000000 : ℝ)^6197 := by
    have hnat : (5309332579 : ℕ)^8245*5000000000000^6197 ≤ 2153478033571^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309332579 10000000000 2153478033571 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406141969/10000000000 : ℝ)^8245 ≤ (44117553817713/100000000000000 : ℝ)^6197 := by
    have hnat : (5406141969 : ℕ)^8245*100000000000000^6197 ≤ 44117553817713^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406141969 10000000000 44117553817713 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213452461/1000000000 : ℝ)^8245 ≤ (2562577097591/20000000000000 : ℝ)^6197 := by
    have hnat : (213452461 : ℕ)^8245*20000000000000^6197 ≤ 2562577097591^6197*1000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213452461 1000000000 2562577097591 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309332579/10000000000 : ℝ), (5406141969/10000000000 : ℝ), (-213452461/1000000000 : ℝ)] ![(2153478033571/5000000000000 : ℝ), (44117553817713/100000000000000 : ℝ), (2562577097591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309332579/10000000000 : ℝ)|^8245 ≤ (2153478033571/5000000000000 : ℝ)^6197
        have hw : |(5309332579/10000000000 : ℝ)|=(5309332579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406141969/10000000000 : ℝ)|^8245 ≤ (44117553817713/100000000000000 : ℝ)^6197
        have hw : |(5406141969/10000000000 : ℝ)|=(5406141969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213452461/1000000000 : ℝ)|^8245 ≤ (2562577097591/20000000000000 : ℝ)^6197
        have hw : |(-213452461/1000000000 : ℝ)|=(213452461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s4_7 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376879033/10000000000 : ℝ)*x 0 + (1132190373/2500000000 : ℝ)*x 1 + (4230202673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376879033/10000000000 : ℝ)^8245 ≤ (6662016499261/20000000000000 : ℝ)^6197 := by
    have hnat : (4376879033 : ℕ)^8245*20000000000000^6197 ≤ 6662016499261^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376879033 10000000000 6662016499261 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132190373/2500000000 : ℝ)^8245 ≤ (34856733041449/100000000000000 : ℝ)^6197 := by
    have hnat : (1132190373 : ℕ)^8245*100000000000000^6197 ≤ 34856733041449^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132190373 2500000000 34856733041449 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230202673/10000000000 : ℝ)^8245 ≤ (31833184445881/100000000000000 : ℝ)^6197 := by
    have hnat : (4230202673 : ℕ)^8245*100000000000000^6197 ≤ 31833184445881^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230202673 10000000000 31833184445881 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376879033/10000000000 : ℝ), (1132190373/2500000000 : ℝ), (4230202673/10000000000 : ℝ)] ![(6662016499261/20000000000000 : ℝ), (34856733041449/100000000000000 : ℝ), (31833184445881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376879033/10000000000 : ℝ)|^8245 ≤ (6662016499261/20000000000000 : ℝ)^6197
        have hw : |(4376879033/10000000000 : ℝ)|=(4376879033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132190373/2500000000 : ℝ)|^8245 ≤ (34856733041449/100000000000000 : ℝ)^6197
        have hw : |(1132190373/2500000000 : ℝ)|=(1132190373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230202673/10000000000 : ℝ)|^8245 ≤ (31833184445881/100000000000000 : ℝ)^6197
        have hw : |(4230202673/10000000000 : ℝ)|=(4230202673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1052_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7463/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (687/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7123/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7463/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7463/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7463/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7463/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7463/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7463/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10349/100000 : ℝ) ^ (2061/512 : ℝ) ≤ (2707205419797597/25000000000000000000 : ℝ) := by
    have hpowers : (10349/100000 : ℝ)^2061 ≤ (2707205419797597/25000000000000000000 : ℝ)^512 := by
      have hnat : (10349 : ℕ)^2061*25000000000000000000^512 ≤ 2707205419797597^512*100000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10349 100000 2707205419797597 25000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10349/100000 : ℝ)) (X := (2707205419797597/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7463/50000 : ℝ) ^ (2061/512 : ℝ) ≤ (1891732164410421/4000000000000000000 : ℝ) := by
    have hpowers : (7463/50000 : ℝ)^2061 ≤ (1891732164410421/4000000000000000000 : ℝ)^512 := by
      have hnat : (7463 : ℕ)^2061*4000000000000000000^512 ≤ 1891732164410421^512*50000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7463 50000 1891732164410421 4000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7463/50000 : ℝ)) (X := (1891732164410421/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502707205419797597/12500000000000000000 : ℝ) ≤ (5000268991048941/5000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (12502707205419797597/12500000000000000000 : ℝ)^512 ≤ (5000268991048941/5000000000000000 : ℝ)^2061 := by
      have hnat : (12502707205419797597 : ℕ)^512*5000000000000000^2061 ≤ 5000268991048941^2061*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502707205419797597 12500000000000000000 5000268991048941 5000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268991048941/5000000000000000 : ℝ)) (X := (12502707205419797597/12500000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058122125789450913/100000000000000000000 : ℝ) ≤ (10001443572579487/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (100058122125789450913/100000000000000000000 : ℝ)^512 ≤ (10001443572579487/10000000000000000 : ℝ)^2061 := by
      have hnat : (100058122125789450913 : ℕ)^512*10000000000000000^2061 ≤ 10001443572579487^2061*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058122125789450913 100000000000000000000 10001443572579487 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001443572579487/10000000000000000 : ℝ)) (X := (100058122125789450913/100000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001891732164410421/2000000000000000000 : ℝ) ≤ (2500587290765273/2500000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (2001891732164410421/2000000000000000000 : ℝ)^512 ≤ (2500587290765273/2500000000000000 : ℝ)^2061 := by
      have hnat : (2001891732164410421 : ℕ)^512*2500000000000000^2061 ≤ 2500587290765273^2061*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001891732164410421 2000000000000000000 2500587290765273 2500000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500587290765273/2500000000000000 : ℝ)) (X := (2001891732164410421/2000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2707205419797597/25000000000000000000 : ℝ) ≤ ((5719214804034218203/5721250000000000000 : ℝ)+2*(181118096321/91540000000000 : ℝ)*(10349/100000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (5719214804034218203/5721250000000000000 : ℝ)+2*(181118096321/91540000000000 : ℝ)*(10349/100000 : ℝ)=(5000268991048941/5000000000000000 : ℝ) by norm_num, show 1+2*(2707205419797597/25000000000000000000 : ℝ)=(12502707205419797597/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1891732164410421/4000000000000000000 : ℝ)+(2707205419797597/25000000000000000000 : ℝ) ≤ ((5719214804034218203/5721250000000000000 : ℝ)+(181118096321/91540000000000 : ℝ)*((7463/50000 : ℝ)+(10349/100000 : ℝ)))^(2061/512 : ℝ) := by
    rw [show (5719214804034218203/5721250000000000000 : ℝ)+(181118096321/91540000000000 : ℝ)*((7463/50000 : ℝ)+(10349/100000 : ℝ))=(10001443572579487/10000000000000000 : ℝ) by norm_num, show 1+(1891732164410421/4000000000000000000 : ℝ)+(2707205419797597/25000000000000000000 : ℝ)=(100058122125789450913/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1891732164410421/4000000000000000000 : ℝ) ≤ ((5719214804034218203/5721250000000000000 : ℝ)+2*(181118096321/91540000000000 : ℝ)*(7463/50000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (5719214804034218203/5721250000000000000 : ℝ)+2*(181118096321/91540000000000 : ℝ)*(7463/50000 : ℝ)=(2500587290765273/2500000000000000 : ℝ) by norm_num, show 1+2*(1891732164410421/4000000000000000000 : ℝ)=(2001891732164410421/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5719214804034218203/5721250000000000000 : ℝ)*(X 1 0+X 2 0)+(181118096321/91540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (10349/100000 : ℝ)) (hi := (7463/50000 : ℝ)) (c := (5719214804034218203/5721250000000000000 : ℝ)) (alpha := (181118096321/91540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5719214804034218203/5721250000000000000 : ℝ)*(X 0 1+X 2 1)+(181118096321/91540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (10349/100000 : ℝ)) (hi := (7463/50000 : ℝ)) (c := (5719214804034218203/5721250000000000000 : ℝ)) (alpha := (181118096321/91540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5719214804034218203/5721250000000000000 : ℝ)*(X 0 2+X 1 2)+(181118096321/91540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (10349/100000 : ℝ)) (hi := (7463/50000 : ℝ)) (c := (5719214804034218203/5721250000000000000 : ℝ)) (alpha := (181118096321/91540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209565021/10000000000 : ℝ)*X 0 0+(2703298417/5000000000 : ℝ)*X 0 1+(1050585571/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668499197/1250000000 : ℝ)*X 1 0+(-35745917/156250000 : ℝ)*X 1 1+(5252927867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347993579/10000000000 : ℝ)*X 2 0+(5252927873/10000000000 : ℝ)*X 2 1+(-571934669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376862857/10000000000 : ℝ)*X 0 0+(1057328413/2500000000 : ℝ)*X 0 1+(1132411659/2500000000 : ℝ)*X 0 2+(4376862857/10000000000 : ℝ)*X 1 0+(1057328413/2500000000 : ℝ)*X 1 1+(1132411659/2500000000 : ℝ)*X 1 2+(4376862857/10000000000 : ℝ)*X 2 0+(1057328413/2500000000 : ℝ)*X 2 1+(1132411659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2209573399/10000000000 : ℝ)*X 0 0+(3283363/6250000 : ℝ)*X 0 1+(5406141939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327333139/2500000000 : ℝ)*X 1 0+(-533631153/2500000000 : ℝ)*X 1 1+(675767749/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309332579/10000000000 : ℝ)*X 2 0+(5406141969/10000000000 : ℝ)*X 2 1+(-213452461/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376879033/10000000000 : ℝ)*X 0 0+(1132190373/2500000000 : ℝ)*X 0 1+(4230202673/10000000000 : ℝ)*X 0 2+(4376879033/10000000000 : ℝ)*X 1 0+(1132190373/2500000000 : ℝ)*X 1 1+(4230202673/10000000000 : ℝ)*X 1 2+(4376879033/10000000000 : ℝ)*X 2 0+(1132190373/2500000000 : ℝ)*X 2 1+(4230202673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1219127530454477873036510217/286062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (918155081/100000000000000 : ℝ)*(base19) + (170225203/20000000000000 : ℝ)*(base23) + (37799361/100000000000000 : ℝ)*(lower2) + (57498497/50000000000000 : ℝ)*(upper3) + (77937193/100000000000000 : ℝ)*(upper5) + (4918598703125787/100000000000000 : ℝ)*(major0) + (4918598703125787/100000000000000 : ℝ)*(major1) + (4918598703125787/100000000000000 : ℝ)*(major2) + (6507516187792129/100000000000000 : ℝ)*(sp0) + (3253768360558619/50000000000000 : ℝ)*(sp1) + (50840131157393/781250000000 : ℝ)*(sp2) + (3329648093288211/100000000000000 : ℝ)*(sp3) + (2145148019/10000000000000 : ℝ)*(sp4) + (5765816313/50000000000000 : ℝ)*(sp7) + (3329659624920837/100000000000000 : ℝ)*(f.failure) + (6507537639272319/100000000000000 : ℝ)*(f.sum) + (819556847449/915400000000000000000000000 : ℝ)*base65 + (5418642642447038261/572125000000000000000000000000000 : ℝ)*base67 + (24880969287913261/572125000000000000000000000000000 : ℝ)*base69 + (3741225680188163261/572125000000000000000000000000000 : ℝ)*base71 + (10261781846487/4577000000000000000000000000 : ℝ)*base73 + (12964490351569211739/572125000000000000000000000000000 : ℝ)*base76 + (4690591761493836739/572125000000000000000000000000000 : ℝ)*base78 + (5157948275939288261/572125000000000000000000000000000 : ℝ)*base79 + (11571758452603/4577000000000000000000000000 : ℝ)*base82 + (15500571/5000000000000000000000 : ℝ)*base89 + (15500571/5000000000000000000000 : ℝ)*base91 + (15500571/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49439472759023066469339/4577000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1993949641/100000000000000 : ℝ)*(base19) + (207565289/10000000000000 : ℝ)*(base23) + (238569951/100000000000000 : ℝ)*(upper3) + (4914011/25000000000000 : ℝ)*(lower4) + (203892447/100000000000000 : ℝ)*(upper5) + (2473897684206633/50000000000000 : ℝ)*(major0) + (2473897684206633/50000000000000 : ℝ)*(major1) + (2473897684206633/50000000000000 : ℝ)*(major2) + (46478539847/100000000000000 : ℝ)*(sp1) + (1948811739/4000000000000 : ℝ)*(sp2) + (6546165984796249/100000000000000 : ℝ)*(sp4) + (163652937807669/2500000000000 : ℝ)*(sp5) + (1309223037769977/20000000000000 : ℝ)*(sp6) + (1674712195986469/50000000000000 : ℝ)*(sp7) + (1674712195986469/50000000000000 : ℝ)*(f.failure) + (6546165984796249/100000000000000 : ℝ)*(f.sum) + (4332861175691/915400000000000000000000000 : ℝ)*base65 + (2395547264312002999/286062500000000000000000000000000 : ℝ)*base67 + (3507903776903809501/286062500000000000000000000000000 : ℝ)*base70 + (2992849285741377999/286062500000000000000000000000000 : ℝ)*base71 + (7624135079947/2288500000000000000000000000 : ℝ)*base74 + (1708254683857934501/286062500000000000000000000000000 : ℝ)*base76 + (668992244515377999/286062500000000000000000000000000 : ℝ)*base77 + (4269203524692997001/286062500000000000000000000000000 : ℝ)*base80 + (13208369573281/2288500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (13157627/2500000000000000000000 : ℝ)*base89 + (13157627/2500000000000000000000 : ℝ)*base91 + (13157627/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1052_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7463/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1052_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1052_s5_0 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-276303907/1250000000 : ℝ)*x 0 + (5397405419/10000000000 : ℝ)*x 1 + (1052310329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276303907/1250000000 : ℝ)^8245 ≤ (13422646198591/100000000000000 : ℝ)^6197 := by
    have hnat : (276303907 : ℕ)^8245*100000000000000^6197 ≤ 13422646198591^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276303907 1250000000 13422646198591 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397405419/10000000000 : ℝ)^8245 ≤ (8804544268839/20000000000000 : ℝ)^6197 := by
    have hnat : (5397405419 : ℕ)^8245*20000000000000^6197 ≤ 8804544268839^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397405419 10000000000 8804544268839 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052310329/2000000000 : ℝ)^8245 ≤ (42554632447919/100000000000000 : ℝ)^6197 := by
    have hnat : (1052310329 : ℕ)^8245*100000000000000^6197 ≤ 42554632447919^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052310329 2000000000 42554632447919 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276303907/1250000000 : ℝ), (5397405419/10000000000 : ℝ), (1052310329/2000000000 : ℝ)] ![(13422646198591/100000000000000 : ℝ), (8804544268839/20000000000000 : ℝ), (42554632447919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276303907/1250000000 : ℝ)|^8245 ≤ (13422646198591/100000000000000 : ℝ)^6197
        have hw : |(-276303907/1250000000 : ℝ)|=(276303907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397405419/10000000000 : ℝ)|^8245 ≤ (8804544268839/20000000000000 : ℝ)^6197
        have hw : |(5397405419/10000000000 : ℝ)|=(5397405419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052310329/2000000000 : ℝ)|^8245 ≤ (42554632447919/100000000000000 : ℝ)^6197
        have hw : |(1052310329/2000000000 : ℝ)|=(1052310329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s5_1 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336427277/2500000000 : ℝ)*x 0 + (-2279405151/10000000000 : ℝ)*x 1 + (1315387849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336427277/2500000000 : ℝ)^8245 ≤ (43462614098011/100000000000000 : ℝ)^6197 := by
    have hnat : (1336427277 : ℕ)^8245*100000000000000^6197 ≤ 43462614098011^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336427277 2500000000 43462614098011 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279405151/10000000000 : ℝ)^8245 ≤ (1398275612239/10000000000000 : ℝ)^6197 := by
    have hnat : (2279405151 : ℕ)^8245*10000000000000^6197 ≤ 1398275612239^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279405151 10000000000 1398275612239 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315387849/2500000000 : ℝ)^8245 ≤ (8510925953699/20000000000000 : ℝ)^6197 := by
    have hnat : (1315387849 : ℕ)^8245*20000000000000^6197 ≤ 8510925953699^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315387849 2500000000 8510925953699 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336427277/2500000000 : ℝ), (-2279405151/10000000000 : ℝ), (1315387849/2500000000 : ℝ)] ![(43462614098011/100000000000000 : ℝ), (1398275612239/10000000000000 : ℝ), (8510925953699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336427277/2500000000 : ℝ)|^8245 ≤ (43462614098011/100000000000000 : ℝ)^6197
        have hw : |(1336427277/2500000000 : ℝ)|=(1336427277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279405151/10000000000 : ℝ)|^8245 ≤ (1398275612239/10000000000000 : ℝ)^6197
        have hw : |(-2279405151/10000000000 : ℝ)|=(2279405151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315387849/2500000000 : ℝ)|^8245 ≤ (8510925953699/20000000000000 : ℝ)^6197
        have hw : |(1315387849/2500000000 : ℝ)|=(1315387849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s5_2 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83526701/156250000 : ℝ)*x 0 + (657693953/1250000000 : ℝ)*x 1 + (-2279405173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83526701/156250000 : ℝ)^8245 ≤ (8692522291717/20000000000000 : ℝ)^6197 := by
    have hnat : (83526701 : ℕ)^8245*20000000000000^6197 ≤ 8692522291717^6197*156250000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83526701 156250000 8692522291717 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657693953/1250000000 : ℝ)^8245 ≤ (42554632221943/100000000000000 : ℝ)^6197 := by
    have hnat : (657693953 : ℕ)^8245*100000000000000^6197 ≤ 42554632221943^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657693953 1250000000 42554632221943 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279405173/10000000000 : ℝ)^8245 ≤ (3495689075487/25000000000000 : ℝ)^6197 := by
    have hnat : (2279405173 : ℕ)^8245*25000000000000^6197 ≤ 3495689075487^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279405173 10000000000 3495689075487 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83526701/156250000 : ℝ), (657693953/1250000000 : ℝ), (-2279405173/10000000000 : ℝ)] ![(8692522291717/20000000000000 : ℝ), (42554632221943/100000000000000 : ℝ), (3495689075487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83526701/156250000 : ℝ)|^8245 ≤ (8692522291717/20000000000000 : ℝ)^6197
        have hw : |(83526701/156250000 : ℝ)|=(83526701/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657693953/1250000000 : ℝ)|^8245 ≤ (42554632221943/100000000000000 : ℝ)^6197
        have hw : |(657693953/1250000000 : ℝ)|=(657693953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2279405173/10000000000 : ℝ)|^8245 ≤ (3495689075487/25000000000000 : ℝ)^6197
        have hw : |(-2279405173/10000000000 : ℝ)|=(2279405173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s5_3 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094341867/2500000000 : ℝ)*x 0 + (530832019/1250000000 : ℝ)*x 1 + (564021419/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094341867/2500000000 : ℝ)^8245 ≤ (1665751413997/5000000000000 : ℝ)^6197 := by
    have hnat : (1094341867 : ℕ)^8245*5000000000000^6197 ≤ 1665751413997^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094341867 2500000000 1665751413997 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530832019/1250000000 : ℝ)^8245 ≤ (7999506301581/25000000000000 : ℝ)^6197 := by
    have hnat : (530832019 : ℕ)^8245*25000000000000^6197 ≤ 7999506301581^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530832019 1250000000 7999506301581 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564021419/1250000000 : ℝ)^8245 ≤ (3468694650017/10000000000000 : ℝ)^6197 := by
    have hnat : (564021419 : ℕ)^8245*10000000000000^6197 ≤ 3468694650017^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564021419 1250000000 3468694650017 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094341867/2500000000 : ℝ), (530832019/1250000000 : ℝ), (564021419/1250000000 : ℝ)] ![(1665751413997/5000000000000 : ℝ), (7999506301581/25000000000000 : ℝ), (3468694650017/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094341867/2500000000 : ℝ)|^8245 ≤ (1665751413997/5000000000000 : ℝ)^6197
        have hw : |(1094341867/2500000000 : ℝ)|=(1094341867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530832019/1250000000 : ℝ)|^8245 ≤ (7999506301581/25000000000000 : ℝ)^6197
        have hw : |(530832019/1250000000 : ℝ)|=(530832019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564021419/1250000000 : ℝ)|^8245 ≤ (3468694650017/10000000000000 : ℝ)^6197
        have hw : |(564021419/1250000000 : ℝ)|=(564021419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s5_4 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210437199/10000000000 : ℝ)*x 0 + (5261905723/10000000000 : ℝ)*x 1 + (5397049879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210437199/10000000000 : ℝ)^8245 ≤ (13422694213511/100000000000000 : ℝ)^6197 := by
    have hnat : (2210437199 : ℕ)^8245*100000000000000^6197 ≤ 13422694213511^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210437199 10000000000 13422694213511 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261905723/10000000000 : ℝ)^8245 ≤ (8511688526373/20000000000000 : ℝ)^6197 := by
    have hnat : (5261905723 : ℕ)^8245*20000000000000^6197 ≤ 8511688526373^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261905723 10000000000 8511688526373 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397049879/10000000000 : ℝ)^8245 ≤ (550235789301/1250000000000 : ℝ)^6197 := by
    have hnat : (5397049879 : ℕ)^8245*1250000000000^6197 ≤ 550235789301^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397049879 10000000000 550235789301 1250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210437199/10000000000 : ℝ), (5261905723/10000000000 : ℝ), (5397049879/10000000000 : ℝ)] ![(13422694213511/100000000000000 : ℝ), (8511688526373/20000000000000 : ℝ), (550235789301/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210437199/10000000000 : ℝ)|^8245 ≤ (13422694213511/100000000000000 : ℝ)^6197
        have hw : |(-2210437199/10000000000 : ℝ)|=(2210437199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261905723/10000000000 : ℝ)|^8245 ≤ (8511688526373/20000000000000 : ℝ)^6197
        have hw : |(5261905723/10000000000 : ℝ)|=(5261905723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397049879/10000000000 : ℝ)|^8245 ≤ (550235789301/1250000000000 : ℝ)^6197
        have hw : |(5397049879/10000000000 : ℝ)|=(5397049879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s5_5 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062305731/2000000000 : ℝ)*x 0 + (-2143907033/10000000000 : ℝ)*x 1 + (539704989/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062305731/2000000000 : ℝ)^8245 ≤ (43093264402979/100000000000000 : ℝ)^6197 := by
    have hnat : (1062305731 : ℕ)^8245*100000000000000^6197 ≤ 43093264402979^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062305731 2000000000 43093264402979 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143907033/10000000000 : ℝ)^8245 ≤ (6443936156673/50000000000000 : ℝ)^6197 := by
    have hnat : (2143907033 : ℕ)^8245*50000000000000^6197 ≤ 6443936156673^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143907033 10000000000 6443936156673 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539704989/1000000000 : ℝ)^8245 ≤ (44018863263447/100000000000000 : ℝ)^6197 := by
    have hnat : (539704989 : ℕ)^8245*100000000000000^6197 ≤ 44018863263447^6197*1000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539704989 1000000000 44018863263447 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062305731/2000000000 : ℝ), (-2143907033/10000000000 : ℝ), (539704989/1000000000 : ℝ)] ![(43093264402979/100000000000000 : ℝ), (6443936156673/50000000000000 : ℝ), (44018863263447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062305731/2000000000 : ℝ)|^8245 ≤ (43093264402979/100000000000000 : ℝ)^6197
        have hw : |(1062305731/2000000000 : ℝ)|=(1062305731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2143907033/10000000000 : ℝ)|^8245 ≤ (6443936156673/50000000000000 : ℝ)^6197
        have hw : |(-2143907033/10000000000 : ℝ)|=(2143907033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539704989/1000000000 : ℝ)|^8245 ≤ (44018863263447/100000000000000 : ℝ)^6197
        have hw : |(539704989/1000000000 : ℝ)|=(539704989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s5_6 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311528733/10000000000 : ℝ)*x 0 + (67463123/125000000 : ℝ)*x 1 + (-428781399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311528733/10000000000 : ℝ)^8245 ≤ (43093265244943/100000000000000 : ℝ)^6197 := by
    have hnat : (5311528733 : ℕ)^8245*100000000000000^6197 ≤ 43093265244943^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311528733 10000000000 43093265244943 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67463123/125000000 : ℝ)^8245 ≤ (4401886272087/10000000000000 : ℝ)^6197 := by
    have hnat : (67463123 : ℕ)^8245*10000000000000^6197 ≤ 4401886272087^6197*125000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67463123 125000000 4401886272087 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428781399/2000000000 : ℝ)^8245 ≤ (644393600471/5000000000000 : ℝ)^6197 := by
    have hnat : (428781399 : ℕ)^8245*5000000000000^6197 ≤ 644393600471^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428781399 2000000000 644393600471 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311528733/10000000000 : ℝ), (67463123/125000000 : ℝ), (-428781399/2000000000 : ℝ)] ![(43093265244943/100000000000000 : ℝ), (4401886272087/10000000000000 : ℝ), (644393600471/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311528733/10000000000 : ℝ)|^8245 ≤ (43093265244943/100000000000000 : ℝ)^6197
        have hw : |(5311528733/10000000000 : ℝ)|=(5311528733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67463123/125000000 : ℝ)|^8245 ≤ (4401886272087/10000000000000 : ℝ)^6197
        have hw : |(67463123/125000000 : ℝ)|=(67463123/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428781399/2000000000 : ℝ)|^8245 ≤ (644393600471/5000000000000 : ℝ)^6197
        have hw : |(-428781399/2000000000 : ℝ)|=(428781399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s5_7 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377378803/10000000000 : ℝ)*x 0 + (563934851/1250000000 : ℝ)*x 1 + (424735123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377378803/10000000000 : ℝ)^8245 ≤ (16657571528891/50000000000000 : ℝ)^6197 := by
    have hnat : (4377378803 : ℕ)^8245*50000000000000^6197 ≤ 16657571528891^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377378803 10000000000 16657571528891 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563934851/1250000000 : ℝ)^8245 ≤ (4334982919653/12500000000000 : ℝ)^6197 := by
    have hnat : (563934851 : ℕ)^8245*12500000000000^6197 ≤ 4334982919653^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563934851 1250000000 4334982919653 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424735123/1000000000 : ℝ)^8245 ≤ (1600249678277/5000000000000 : ℝ)^6197 := by
    have hnat : (424735123 : ℕ)^8245*5000000000000^6197 ≤ 1600249678277^6197*1000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424735123 1000000000 1600249678277 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377378803/10000000000 : ℝ), (563934851/1250000000 : ℝ), (424735123/1000000000 : ℝ)] ![(16657571528891/50000000000000 : ℝ), (4334982919653/12500000000000 : ℝ), (1600249678277/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377378803/10000000000 : ℝ)|^8245 ≤ (16657571528891/50000000000000 : ℝ)^6197
        have hw : |(4377378803/10000000000 : ℝ)|=(4377378803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563934851/1250000000 : ℝ)|^8245 ≤ (4334982919653/12500000000000 : ℝ)^6197
        have hw : |(563934851/1250000000 : ℝ)|=(563934851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424735123/1000000000 : ℝ)|^8245 ≤ (1600249678277/5000000000000 : ℝ)^6197
        have hw : |(424735123/1000000000 : ℝ)|=(424735123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1052_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1397/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (687/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (687/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (687/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (687/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (687/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (687/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (687/6250 : ℝ) ^ (2061/512 : ℝ) ≤ (1725318306621181/12500000000000000000 : ℝ) := by
    have hpowers : (687/6250 : ℝ)^2061 ≤ (1725318306621181/12500000000000000000 : ℝ)^512 := by
      have hnat : (687 : ℕ)^2061*12500000000000000000^512 ≤ 1725318306621181^512*6250^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        687 6250 1725318306621181 12500000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (687/6250 : ℝ)) (X := (1725318306621181/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7123/50000 : ℝ) ^ (2061/512 : ℝ) ≤ (4899970979020409/12500000000000000000 : ℝ) := by
    have hpowers : (7123/50000 : ℝ)^2061 ≤ (4899970979020409/12500000000000000000 : ℝ)^512 := by
      have hnat : (7123 : ℕ)^2061*12500000000000000000^512 ≤ 4899970979020409^512*50000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7123 50000 4899970979020409 12500000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7123/50000 : ℝ)) (X := (4899970979020409/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251725318306621181/6250000000000000000 : ℝ) ≤ (1000068570313483/1000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (6251725318306621181/6250000000000000000 : ℝ)^512 ≤ (1000068570313483/1000000000000000 : ℝ)^2061 := by
      have hnat : (6251725318306621181 : ℕ)^512*1000000000000000^2061 ≤ 1000068570313483^2061*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251725318306621181 6250000000000000000 1000068570313483 1000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000068570313483/1000000000000000 : ℝ)) (X := (6251725318306621181/6250000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250662528928564159/1250000000000000000 : ℝ) ≤ (10001316437724137/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (1250662528928564159/1250000000000000000 : ℝ)^512 ≤ (10001316437724137/10000000000000000 : ℝ)^2061 := by
      have hnat : (1250662528928564159 : ℕ)^512*10000000000000000^2061 ≤ 10001316437724137^2061*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250662528928564159 1250000000000000000 10001316437724137 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001316437724137/10000000000000000 : ℝ)) (X := (1250662528928564159/1250000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254899970979020409/6250000000000000000 : ℝ) ≤ (2500486793078361/2500000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (6254899970979020409/6250000000000000000 : ℝ)^512 ≤ (2500486793078361/2500000000000000 : ℝ)^2061 := by
      have hnat : (6254899970979020409 : ℕ)^512*2500000000000000^2061 ≤ 2500486793078361^2061*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254899970979020409 6250000000000000000 2500486793078361 2500000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500486793078361/2500000000000000 : ℝ)) (X := (6254899970979020409/6250000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1725318306621181/12500000000000000000 : ℝ) ≤ ((8132091302197352933/8135000000000000000 : ℝ)+2*(630734589307/325400000000000 : ℝ)*(687/6250 : ℝ))^(2061/512 : ℝ) := by
    rw [show (8132091302197352933/8135000000000000000 : ℝ)+2*(630734589307/325400000000000 : ℝ)*(687/6250 : ℝ)=(1000068570313483/1000000000000000 : ℝ) by norm_num, show 1+2*(1725318306621181/12500000000000000000 : ℝ)=(6251725318306621181/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4899970979020409/12500000000000000000 : ℝ)+(1725318306621181/12500000000000000000 : ℝ) ≤ ((8132091302197352933/8135000000000000000 : ℝ)+(630734589307/325400000000000 : ℝ)*((7123/50000 : ℝ)+(687/6250 : ℝ)))^(2061/512 : ℝ) := by
    rw [show (8132091302197352933/8135000000000000000 : ℝ)+(630734589307/325400000000000 : ℝ)*((7123/50000 : ℝ)+(687/6250 : ℝ))=(10001316437724137/10000000000000000 : ℝ) by norm_num, show 1+(4899970979020409/12500000000000000000 : ℝ)+(1725318306621181/12500000000000000000 : ℝ)=(1250662528928564159/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4899970979020409/12500000000000000000 : ℝ) ≤ ((8132091302197352933/8135000000000000000 : ℝ)+2*(630734589307/325400000000000 : ℝ)*(7123/50000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (8132091302197352933/8135000000000000000 : ℝ)+2*(630734589307/325400000000000 : ℝ)*(7123/50000 : ℝ)=(2500486793078361/2500000000000000 : ℝ) by norm_num, show 1+2*(4899970979020409/12500000000000000000 : ℝ)=(6254899970979020409/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8132091302197352933/8135000000000000000 : ℝ)*(X 1 0+X 2 0)+(630734589307/325400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (8132091302197352933/8135000000000000000 : ℝ)) (alpha := (630734589307/325400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8132091302197352933/8135000000000000000 : ℝ)*(X 0 1+X 2 1)+(630734589307/325400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (8132091302197352933/8135000000000000000 : ℝ)) (alpha := (630734589307/325400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8132091302197352933/8135000000000000000 : ℝ)*(X 0 2+X 1 2)+(630734589307/325400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (8132091302197352933/8135000000000000000 : ℝ)) (alpha := (630734589307/325400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276303907/1250000000 : ℝ)*X 0 0+(5397405419/10000000000 : ℝ)*X 0 1+(1052310329/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336427277/2500000000 : ℝ)*X 1 0+(-2279405151/10000000000 : ℝ)*X 1 1+(1315387849/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83526701/156250000 : ℝ)*X 2 0+(657693953/1250000000 : ℝ)*X 2 1+(-2279405173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094341867/2500000000 : ℝ)*X 0 0+(530832019/1250000000 : ℝ)*X 0 1+(564021419/1250000000 : ℝ)*X 0 2+(1094341867/2500000000 : ℝ)*X 1 0+(530832019/1250000000 : ℝ)*X 1 1+(564021419/1250000000 : ℝ)*X 1 2+(1094341867/2500000000 : ℝ)*X 2 0+(530832019/1250000000 : ℝ)*X 2 1+(564021419/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2210437199/10000000000 : ℝ)*X 0 0+(5261905723/10000000000 : ℝ)*X 0 1+(5397049879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062305731/2000000000 : ℝ)*X 1 0+(-2143907033/10000000000 : ℝ)*X 1 1+(539704989/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311528733/10000000000 : ℝ)*X 2 0+(67463123/125000000 : ℝ)*X 2 1+(-428781399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377378803/10000000000 : ℝ)*X 0 0+(563934851/1250000000 : ℝ)*X 0 1+(424735123/1000000000 : ℝ)*X 0 2+(4377378803/10000000000 : ℝ)*X 1 0+(563934851/1250000000 : ℝ)*X 1 1+(424735123/1000000000 : ℝ)*X 1 2+(4377378803/10000000000 : ℝ)*X 2 0+(563934851/1250000000 : ℝ)*X 2 1+(424735123/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1270294680828286379554811379/406750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (753290631/100000000000000 : ℝ)*(base19) + (116489299/25000000000000 : ℝ)*(base23) + (46854001/100000000000000 : ℝ)*(lower2) + (14571911/20000000000000 : ℝ)*(lower4) + (59399893/100000000000000 : ℝ)*(lower5) + (5563587147952193/100000000000000 : ℝ)*(major0) + (5563587147952193/100000000000000 : ℝ)*(major1) + (5563587147952193/100000000000000 : ℝ)*(major2) + (7360874956602083/100000000000000 : ℝ)*(sp0) + (7360887019477747/100000000000000 : ℝ)*(sp1) + (3680443653405591/50000000000000 : ℝ)*(sp2) + (470784370065523/12500000000000 : ℝ)*(sp3) + (2563233259/20000000000000 : ℝ)*(sp4) + (11458510627/100000000000000 : ℝ)*(sp7) + (941571604758703/25000000000000 : ℝ)*(f.failure) + (3680443886384189/50000000000000 : ℝ)*(f.sum) + (155662276417451/16270000000000000000000000000 : ℝ)*base65 + (15535828014717607069/813500000000000000000000000000000 : ℝ)*base67 + (10112356788795607069/813500000000000000000000000000000 : ℝ)*base69 + (5596372244907107069/813500000000000000000000000000000 : ℝ)*base71 + (167913161005761/16270000000000000000000000000 : ℝ)*base73 + (23269840731573607069/813500000000000000000000000000000 : ℝ)*base75 + (7507692470085107069/813500000000000000000000000000000 : ℝ)*base77 + (12507683675586607069/813500000000000000000000000000000 : ℝ)*base79 + (23444416685411/16270000000000000000000000000 : ℝ)*base81 + (13663249/1250000000000000000000 : ℝ)*base89 + (13663249/1250000000000000000000 : ℝ)*base91 + (13663249/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1416206051302903834373884593/203375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1010965561/100000000000000 : ℝ)*(base19) + (242571341/20000000000000 : ℝ)*(base23) + (85675409/100000000000000 : ℝ)*(upper3) + (21234637/50000000000000 : ℝ)*(lower4) + (16353301/10000000000000 : ℝ)*(upper5) + (2796389462502007/50000000000000 : ℝ)*(major0) + (2796389462502007/50000000000000 : ℝ)*(major1) + (2796389462502007/50000000000000 : ℝ)*(major2) + (14310360327/50000000000000 : ℝ)*(sp1) + (15341740361/50000000000000 : ℝ)*(sp2) + (3699754870454509/50000000000000 : ℝ)*(sp4) + (7399480109222803/100000000000000 : ℝ)*(sp5) + (7399477844571591/100000000000000 : ℝ)*(sp6) + (3786047876981639/100000000000000 : ℝ)*(sp7) + (3786047876981639/100000000000000 : ℝ)*(f.failure) + (3699754870454509/50000000000000 : ℝ)*(f.sum) + (13902176972981/2033750000000000000000000000 : ℝ)*base65 + (3643381981021938469/406750000000000000000000000000000 : ℝ)*base68 + (4964123012067438469/406750000000000000000000000000000 : ℝ)*base70 + (1654325914659061531/406750000000000000000000000000000 : ℝ)*base71 + (1919112051199/508437500000000000000000000 : ℝ)*base73 + (9661868239233438469/406750000000000000000000000000000 : ℝ)*base76 + (794005974014561531/406750000000000000000000000000000 : ℝ)*base77 + (9277023213811438469/406750000000000000000000000000000 : ℝ)*base80 + (3503682504427/1016875000000000000000000000 : ℝ)*base82 + (40507737/5000000000000000000000 : ℝ)*base89 + (40507737/5000000000000000000000 : ℝ)*base91 + (40507737/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1052_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1052_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1052_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1052_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1052_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1052_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1052_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
