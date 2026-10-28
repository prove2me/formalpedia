-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:06.308656+00:00
-- url     : https://prove2.me/submissions/7ef6382f-505e-49c2-93ad-ac4c62993f8a

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
theorem support_rectangle_w1214_s0_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869230481/10000000000 : ℝ)*x 0 + (3018919153/5000000000 : ℝ)*x 1 + (957902059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869230481/10000000000 : ℝ)^8407 ≤ (5445807103781/50000000000000 : ℝ)^6359 := by
    have hnat : (1869230481 : ℕ)^8407*50000000000000^6359 ≤ 5445807103781^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869230481 10000000000 5445807103781 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3018919153/5000000000 : ℝ)^8407 ≤ (801920818629/1562500000000 : ℝ)^6359 := by
    have hnat : (3018919153 : ℕ)^8407*1562500000000^6359 ≤ 801920818629^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3018919153 5000000000 801920818629 1562500000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957902059/2000000000 : ℝ)^8407 ≤ (9446363347063/25000000000000 : ℝ)^6359 := by
    have hnat : (957902059 : ℕ)^8407*25000000000000^6359 ≤ 9446363347063^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957902059 2000000000 9446363347063 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869230481/10000000000 : ℝ), (3018919153/5000000000 : ℝ), (957902059/2000000000 : ℝ)] ![(5445807103781/50000000000000 : ℝ), (801920818629/1562500000000 : ℝ), (9446363347063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869230481/10000000000 : ℝ)|^8407 ≤ (5445807103781/50000000000000 : ℝ)^6359
        have hw : |(-1869230481/10000000000 : ℝ)|=(1869230481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3018919153/5000000000 : ℝ)|^8407 ≤ (801920818629/1562500000000 : ℝ)^6359
        have hw : |(3018919153/5000000000 : ℝ)|=(3018919153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957902059/2000000000 : ℝ)|^8407 ≤ (9446363347063/25000000000000 : ℝ)^6359
        have hw : |(957902059/2000000000 : ℝ)|=(957902059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s0_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5512737/10000000 : ℝ)*x 0 + (-322954023/1250000000 : ℝ)*x 1 + (4789510267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512737/10000000 : ℝ)^8407 ≤ (45506264400641/100000000000000 : ℝ)^6359 := by
    have hnat : (5512737 : ℕ)^8407*100000000000000^6359 ≤ 45506264400641^6359*10000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512737 10000000 45506264400641 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322954023/1250000000 : ℝ)^8407 ≤ (16708282492149/100000000000000 : ℝ)^6359 := by
    have hnat : (322954023 : ℕ)^8407*100000000000000^6359 ≤ 16708282492149^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322954023 1250000000 16708282492149 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789510267/10000000000 : ℝ)^8407 ≤ (37785453096211/100000000000000 : ℝ)^6359 := by
    have hnat : (4789510267 : ℕ)^8407*100000000000000^6359 ≤ 37785453096211^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789510267 10000000000 37785453096211 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512737/10000000 : ℝ), (-322954023/1250000000 : ℝ), (4789510267/10000000000 : ℝ)] ![(45506264400641/100000000000000 : ℝ), (16708282492149/100000000000000 : ℝ), (37785453096211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512737/10000000 : ℝ)|^8407 ≤ (45506264400641/100000000000000 : ℝ)^6359
        have hw : |(5512737/10000000 : ℝ)|=(5512737/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-322954023/1250000000 : ℝ)|^8407 ≤ (16708282492149/100000000000000 : ℝ)^6359
        have hw : |(-322954023/1250000000 : ℝ)|=(322954023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789510267/10000000000 : ℝ)|^8407 ≤ (37785453096211/100000000000000 : ℝ)^6359
        have hw : |(4789510267/10000000000 : ℝ)|=(4789510267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s0_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2756368491/5000000000 : ℝ)*x 0 + (4789510287/10000000000 : ℝ)*x 1 + (-1291816091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756368491/5000000000 : ℝ)^8407 ≤ (22753132102101/50000000000000 : ℝ)^6359 := by
    have hnat : (2756368491 : ℕ)^8407*50000000000000^6359 ≤ 22753132102101^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756368491 5000000000 22753132102101 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4789510287/10000000000 : ℝ)^8407 ≤ (9446363326203/25000000000000 : ℝ)^6359 := by
    have hnat : (4789510287 : ℕ)^8407*25000000000000^6359 ≤ 9446363326203^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789510287 10000000000 9446363326203 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291816091/5000000000 : ℝ)^8407 ≤ (16708282475049/100000000000000 : ℝ)^6359 := by
    have hnat : (1291816091 : ℕ)^8407*100000000000000^6359 ≤ 16708282475049^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291816091 5000000000 16708282475049 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756368491/5000000000 : ℝ), (4789510287/10000000000 : ℝ), (-1291816091/5000000000 : ℝ)] ![(22753132102101/50000000000000 : ℝ), (9446363326203/25000000000000 : ℝ), (16708282475049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756368491/5000000000 : ℝ)|^8407 ≤ (22753132102101/50000000000000 : ℝ)^6359
        have hw : |(2756368491/5000000000 : ℝ)|=(2756368491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4789510287/10000000000 : ℝ)|^8407 ≤ (9446363326203/25000000000000 : ℝ)^6359
        have hw : |(4789510287/10000000000 : ℝ)|=(4789510287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1291816091/5000000000 : ℝ)|^8407 ≤ (16708282475049/100000000000000 : ℝ)^6359
        have hw : |(-1291816091/5000000000 : ℝ)|=(1291816091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s0_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4195229557/10000000000 : ℝ)*x 0 + (3117975167/10000000000 : ℝ)*x 1 + (1409153171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195229557/10000000000 : ℝ)^8407 ≤ (634291982643/2000000000000 : ℝ)^6359 := by
    have hnat : (4195229557 : ℕ)^8407*2000000000000^6359 ≤ 634291982643^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195229557 10000000000 634291982643 2000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117975167/10000000000 : ℝ)^8407 ≤ (214223765971/1000000000000 : ℝ)^6359 := by
    have hnat : (3117975167 : ℕ)^8407*1000000000000^6359 ≤ 214223765971^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117975167 10000000000 214223765971 1000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1409153171/2500000000 : ℝ)^8407 ≤ (11715756064721/25000000000000 : ℝ)^6359 := by
    have hnat : (1409153171 : ℕ)^8407*25000000000000^6359 ≤ 11715756064721^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409153171 2500000000 11715756064721 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195229557/10000000000 : ℝ), (3117975167/10000000000 : ℝ), (1409153171/2500000000 : ℝ)] ![(634291982643/2000000000000 : ℝ), (214223765971/1000000000000 : ℝ), (11715756064721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195229557/10000000000 : ℝ)|^8407 ≤ (634291982643/2000000000000 : ℝ)^6359
        have hw : |(4195229557/10000000000 : ℝ)|=(4195229557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117975167/10000000000 : ℝ)|^8407 ≤ (214223765971/1000000000000 : ℝ)^6359
        have hw : |(3117975167/10000000000 : ℝ)|=(3117975167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1409153171/2500000000 : ℝ)|^8407 ≤ (11715756064721/25000000000000 : ℝ)^6359
        have hw : |(1409153171/2500000000 : ℝ)|=(1409153171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s0_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1874168007/10000000000 : ℝ)*x 0 + (192867001/400000000 : ℝ)*x 1 + (6004537719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1874168007/10000000000 : ℝ)^8407 ≤ (10929666041781/100000000000000 : ℝ)^6359 := by
    have hnat : (1874168007 : ℕ)^8407*100000000000000^6359 ≤ 10929666041781^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874168007 10000000000 10929666041781 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192867001/400000000 : ℝ)^8407 ≤ (9530323721129/25000000000000 : ℝ)^6359 := by
    have hnat : (192867001 : ℕ)^8407*25000000000000^6359 ≤ 9530323721129^6359*400000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192867001 400000000 9530323721129 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004537719/10000000000 : ℝ)^8407 ≤ (50949039053991/100000000000000 : ℝ)^6359 := by
    have hnat : (6004537719 : ℕ)^8407*100000000000000^6359 ≤ 50949039053991^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004537719 10000000000 50949039053991 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1874168007/10000000000 : ℝ), (192867001/400000000 : ℝ), (6004537719/10000000000 : ℝ)] ![(10929666041781/100000000000000 : ℝ), (9530323721129/25000000000000 : ℝ), (50949039053991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1874168007/10000000000 : ℝ)|^8407 ≤ (10929666041781/100000000000000 : ℝ)^6359
        have hw : |(-1874168007/10000000000 : ℝ)|=(1874168007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192867001/400000000 : ℝ)|^8407 ≤ (9530323721129/25000000000000 : ℝ)^6359
        have hw : |(192867001/400000000 : ℝ)|=(192867001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004537719/10000000000 : ℝ)|^8407 ≤ (50949039053991/100000000000000 : ℝ)^6359
        have hw : |(6004537719/10000000000 : ℝ)|=(6004537719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s0_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586602967/5000000000 : ℝ)*x 0 + (-1368603083/10000000000 : ℝ)*x 1 + (6004539469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586602967/5000000000 : ℝ)^8407 ≤ (20919067487203/50000000000000 : ℝ)^6359 := by
    have hnat : (2586602967 : ℕ)^8407*50000000000000^6359 ≤ 20919067487203^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586602967 5000000000 20919067487203 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368603083/10000000000 : ℝ)^8407 ≤ (7212806329121/100000000000000 : ℝ)^6359 := by
    have hnat : (1368603083 : ℕ)^8407*100000000000000^6359 ≤ 7212806329121^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368603083 10000000000 7212806329121 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004539469/10000000000 : ℝ)^8407 ≤ (10189811737037/20000000000000 : ℝ)^6359 := by
    have hnat : (6004539469 : ℕ)^8407*20000000000000^6359 ≤ 10189811737037^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004539469 10000000000 10189811737037 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586602967/5000000000 : ℝ), (-1368603083/10000000000 : ℝ), (6004539469/10000000000 : ℝ)] ![(20919067487203/50000000000000 : ℝ), (7212806329121/100000000000000 : ℝ), (10189811737037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586602967/5000000000 : ℝ)|^8407 ≤ (20919067487203/50000000000000 : ℝ)^6359
        have hw : |(2586602967/5000000000 : ℝ)|=(2586602967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1368603083/10000000000 : ℝ)|^8407 ≤ (7212806329121/100000000000000 : ℝ)^6359
        have hw : |(-1368603083/10000000000 : ℝ)|=(1368603083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004539469/10000000000 : ℝ)|^8407 ≤ (10189811737037/20000000000000 : ℝ)^6359
        have hw : |(6004539469/10000000000 : ℝ)|=(6004539469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s0_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646650851/1250000000 : ℝ)*x 0 + (1501134549/2500000000 : ℝ)*x 1 + (-85537737/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646650851/1250000000 : ℝ)^8407 ≤ (2091907215967/5000000000000 : ℝ)^6359 := by
    have hnat : (646650851 : ℕ)^8407*5000000000000^6359 ≤ 2091907215967^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646650851 1250000000 2091907215967 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1501134549/2500000000 : ℝ)^8407 ≤ (50949044404893/100000000000000 : ℝ)^6359 := by
    have hnat : (1501134549 : ℕ)^8407*100000000000000^6359 ≤ 50949044404893^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501134549 2500000000 50949044404893 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85537737/625000000 : ℝ)^8407 ≤ (3606405634551/50000000000000 : ℝ)^6359 := by
    have hnat : (85537737 : ℕ)^8407*50000000000000^6359 ≤ 3606405634551^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85537737 625000000 3606405634551 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646650851/1250000000 : ℝ), (1501134549/2500000000 : ℝ), (-85537737/625000000 : ℝ)] ![(2091907215967/5000000000000 : ℝ), (50949044404893/100000000000000 : ℝ), (3606405634551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646650851/1250000000 : ℝ)|^8407 ≤ (2091907215967/5000000000000 : ℝ)^6359
        have hw : |(646650851/1250000000 : ℝ)|=(646650851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1501134549/2500000000 : ℝ)|^8407 ≤ (50949044404893/100000000000000 : ℝ)^6359
        have hw : |(1501134549/2500000000 : ℝ)|=(1501134549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85537737/625000000 : ℝ)|^8407 ≤ (3606405634551/50000000000000 : ℝ)^6359
        have hw : |(-85537737/625000000 : ℝ)|=(85537737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s0_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4205190613/10000000000 : ℝ)*x 0 + (2785860407/5000000000 : ℝ)*x 1 + (3185157859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205190613/10000000000 : ℝ)^8407 ≤ (1272567668937/4000000000000 : ℝ)^6359 := by
    have hnat : (4205190613 : ℕ)^8407*4000000000000^6359 ≤ 1272567668937^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205190613 10000000000 1272567668937 4000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785860407/5000000000 : ℝ)^8407 ≤ (46151078935717/100000000000000 : ℝ)^6359 := by
    have hnat : (2785860407 : ℕ)^8407*100000000000000^6359 ≤ 46151078935717^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785860407 5000000000 46151078935717 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185157859/10000000000 : ℝ)^8407 ≤ (22034729319127/100000000000000 : ℝ)^6359 := by
    have hnat : (3185157859 : ℕ)^8407*100000000000000^6359 ≤ 22034729319127^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185157859 10000000000 22034729319127 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205190613/10000000000 : ℝ), (2785860407/5000000000 : ℝ), (3185157859/10000000000 : ℝ)] ![(1272567668937/4000000000000 : ℝ), (46151078935717/100000000000000 : ℝ), (22034729319127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205190613/10000000000 : ℝ)|^8407 ≤ (1272567668937/4000000000000 : ℝ)^6359
        have hw : |(4205190613/10000000000 : ℝ)|=(4205190613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785860407/5000000000 : ℝ)|^8407 ≤ (46151078935717/100000000000000 : ℝ)^6359
        have hw : |(2785860407/5000000000 : ℝ)|=(2785860407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185157859/10000000000 : ℝ)|^8407 ≤ (22034729319127/100000000000000 : ℝ)^6359
        have hw : |(3185157859/10000000000 : ℝ)|=(3185157859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (353/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27541/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4203/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4203 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4203*1^1024 ≤ 0^1024*1^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4203/1024 : ℝ) ≤ (581565120850833719/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4203 ≤ (581565120850833719/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4203*25000000000000000000^1024 ≤ 581565120850833719^1024*5^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 581565120850833719 25000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (581565120850833719/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4203 := by
      have hnat : (1 : ℕ)^1024*1^4203 ≤ 1^4203*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25581565120850833719/25000000000000000000 : ℝ) ≤ (2011236807971547/2000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (25581565120850833719/25000000000000000000 : ℝ)^1024 ≤ (2011236807971547/2000000000000000 : ℝ)^4203 := by
      have hnat : (25581565120850833719 : ℕ)^1024*2000000000000000^4203 ≤ 2011236807971547^4203*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25581565120850833719 25000000000000000000 2011236807971547 2000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011236807971547/2000000000000000 : ℝ)) (X := (25581565120850833719/25000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13081565120850833719/12500000000000000000 : ℝ) ≤ (1011236807971547/1000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (13081565120850833719/12500000000000000000 : ℝ)^1024 ≤ (1011236807971547/1000000000000000 : ℝ)^4203 := by
      have hnat : (13081565120850833719 : ℕ)^1024*1000000000000000^4203 ≤ 1011236807971547^4203*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13081565120850833719 12500000000000000000 1011236807971547 1000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011236807971547/1000000000000000 : ℝ)) (X := (13081565120850833719/12500000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11236807971547/800000000000000 : ℝ)*(0 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11236807971547/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(581565120850833719/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11236807971547/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11236807971547/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011236807971547/2000000000000000 : ℝ) by norm_num, show 1+(581565120850833719/25000000000000000000 : ℝ)+(0 : ℝ)=(25581565120850833719/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(581565120850833719/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11236807971547/800000000000000 : ℝ)*(2/5 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11236807971547/800000000000000 : ℝ)*(2/5 : ℝ)=(1011236807971547/1000000000000000 : ℝ) by norm_num, show 1+2*(581565120850833719/25000000000000000000 : ℝ)=(13081565120850833719/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11236807971547/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11236807971547/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11236807971547/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11236807971547/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11236807971547/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11236807971547/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1869230481/10000000000 : ℝ)*X 0 0+(3018919153/5000000000 : ℝ)*X 0 1+(957902059/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512737/10000000 : ℝ)*X 1 0+(-322954023/1250000000 : ℝ)*X 1 1+(4789510267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2756368491/5000000000 : ℝ)*X 2 0+(4789510287/10000000000 : ℝ)*X 2 1+(-1291816091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4195229557/10000000000 : ℝ)*X 0 0+(3117975167/10000000000 : ℝ)*X 0 1+(1409153171/2500000000 : ℝ)*X 0 2+(4195229557/10000000000 : ℝ)*X 1 0+(3117975167/10000000000 : ℝ)*X 1 1+(1409153171/2500000000 : ℝ)*X 1 2+(4195229557/10000000000 : ℝ)*X 2 0+(3117975167/10000000000 : ℝ)*X 2 1+(1409153171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1874168007/10000000000 : ℝ)*X 0 0+(192867001/400000000 : ℝ)*X 0 1+(6004537719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586602967/5000000000 : ℝ)*X 1 0+(-1368603083/10000000000 : ℝ)*X 1 1+(6004539469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646650851/1250000000 : ℝ)*X 2 0+(1501134549/2500000000 : ℝ)*X 2 1+(-85537737/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4205190613/10000000000 : ℝ)*X 0 0+(2785860407/5000000000 : ℝ)*X 0 1+(3185157859/10000000000 : ℝ)*X 0 2+(4205190613/10000000000 : ℝ)*X 1 0+(2785860407/5000000000 : ℝ)*X 1 1+(3185157859/10000000000 : ℝ)*X 1 2+(4205190613/10000000000 : ℝ)*X 2 0+(2785860407/5000000000 : ℝ)*X 2 1+(3185157859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6063107956847118321/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67575391/100000000000000 : ℝ)*(base1) + (740921123/50000000000000 : ℝ)*(base19) + (1377786621/100000000000000 : ℝ)*(base23) + (25359993/25000000000000 : ℝ)*(base24) + (338593739/100000000000000 : ℝ)*(upper3) + (599062084267719/100000000000000 : ℝ)*(major0) + (599062084267719/100000000000000 : ℝ)*(major1) + (599062084267719/100000000000000 : ℝ)*(major2) + (400538259423989/50000000000000 : ℝ)*(sp0) + (801078252568713/100000000000000 : ℝ)*(sp1) + (400539127592183/50000000000000 : ℝ)*(sp2) + (19852078820221/5000000000000 : ℝ)*(sp3) + (820784593/25000000000000 : ℝ)*(sp4) + (517608213/20000000000000 : ℝ)*(sp7) + (99261058005219/25000000000000 : ℝ)*(f.failure) + (801079734410959/100000000000000 : ℝ)*(f.sum) + (67550027928707/40000000000000000000000000000 : ℝ)*base66 + (464967713151293/80000000000000000000000000000 : ℝ)*base67 + (136589124848707/80000000000000000000000000000 : ℝ)*base70 + (3558380208707/80000000000000000000000000000 : ℝ)*base72 + (6397048271293/40000000000000000000000000000 : ℝ)*base73 + (143787723711293/80000000000000000000000000000 : ℝ)*base75 + (118126226831293/80000000000000000000000000000 : ℝ)*base77 + (657930235231293/80000000000000000000000000000 : ℝ)*base79 + (140253777528707/40000000000000000000000000000 : ℝ)*base82 + (249591/62500000000000000000 : ℝ)*base90 + (249591/62500000000000000000 : ℝ)*base92 + (249591/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76640344425096400171359/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281330947/50000000000000 : ℝ)*(base19) + (832468161/100000000000000 : ℝ)*(base23) + (62165331/50000000000000 : ℝ)*(base39) + (37856861/20000000000000 : ℝ)*(upper3) + (126441792746213/20000000000000 : ℝ)*(major0) + (126441792746213/20000000000000 : ℝ)*(major1) + (632208839400403/100000000000000 : ℝ)*(major2) + (1510011671/100000000000000 : ℝ)*(sp1) + (400444297/25000000000000 : ℝ)*(sp2) + (4765439/100000000000000 : ℝ)*(sp3) + (33816181466843/4000000000000 : ℝ)*(sp4) + (845402463997511/100000000000000 : ℝ)*(sp5) + (211350556689097/25000000000000 : ℝ)*(sp6) + (83802639565599/20000000000000 : ℝ)*(sp7) + (209506601296717/50000000000000 : ℝ)*(f.failure) + (845404661001737/100000000000000 : ℝ)*(f.sum) + (5026532425249/20000000000000000000000000000 : ℝ)*base65 + (224514714893441/80000000000000000000000000000 : ℝ)*base67 + (100671593505511/16000000000000000000000000000 : ℝ)*base69 + (3330265773441/80000000000000000000000000000 : ℝ)*base71 + (39728503765249/20000000000000000000000000000 : ℝ)*base73 + (48573364750489/16000000000000000000000000000 : ℝ)*base76 + (68228734753511/16000000000000000000000000000 : ℝ)*base77 + (73700372049511/16000000000000000000000000000 : ℝ)*base79 + (10843868249511/8000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (462113/125000000000000000000 : ℝ)*base90 + (462113/125000000000000000000 : ℝ)*base92 + (462113/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27541/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1214_s1_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068681473/10000000000 : ℝ)*x 0 + (1136537209/2000000000 : ℝ)*x 1 + (2508495191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068681473/10000000000 : ℝ)^8407 ≤ (778365771037/6250000000000 : ℝ)^6359 := by
    have hnat : (2068681473 : ℕ)^8407*6250000000000^6359 ≤ 778365771037^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068681473 10000000000 778365771037 6250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136537209/2000000000 : ℝ)^8407 ≤ (47370113568169/100000000000000 : ℝ)^6359 := by
    have hnat : (1136537209 : ℕ)^8407*100000000000000^6359 ≤ 47370113568169^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136537209 2000000000 47370113568169 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508495191/5000000000 : ℝ)^8407 ≤ (40176034070653/100000000000000 : ℝ)^6359 := by
    have hnat : (2508495191 : ℕ)^8407*100000000000000^6359 ≤ 40176034070653^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508495191 5000000000 40176034070653 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068681473/10000000000 : ℝ), (1136537209/2000000000 : ℝ), (2508495191/5000000000 : ℝ)] ![(778365771037/6250000000000 : ℝ), (47370113568169/100000000000000 : ℝ), (40176034070653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068681473/10000000000 : ℝ)|^8407 ≤ (778365771037/6250000000000 : ℝ)^6359
        have hw : |(-2068681473/10000000000 : ℝ)|=(2068681473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136537209/2000000000 : ℝ)|^8407 ≤ (47370113568169/100000000000000 : ℝ)^6359
        have hw : |(1136537209/2000000000 : ℝ)|=(1136537209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508495191/5000000000 : ℝ)|^8407 ≤ (40176034070653/100000000000000 : ℝ)^6359
        have hw : |(2508495191/5000000000 : ℝ)|=(2508495191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s1_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5415179859/10000000000 : ℝ)*x 0 + (-2426635527/10000000000 : ℝ)*x 1 + (1003398181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415179859/10000000000 : ℝ)^8407 ≤ (8888928039233/20000000000000 : ℝ)^6359 := by
    have hnat : (5415179859 : ℕ)^8407*20000000000000^6359 ≤ 8888928039233^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415179859 10000000000 8888928039233 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2426635527/10000000000 : ℝ)^8407 ≤ (3844830046419/25000000000000 : ℝ)^6359 := by
    have hnat : (2426635527 : ℕ)^8407*25000000000000^6359 ≤ 3844830046419^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426635527 10000000000 3844830046419 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003398181/2000000000 : ℝ)^8407 ≤ (20088019803847/50000000000000 : ℝ)^6359 := by
    have hnat : (1003398181 : ℕ)^8407*50000000000000^6359 ≤ 20088019803847^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003398181 2000000000 20088019803847 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415179859/10000000000 : ℝ), (-2426635527/10000000000 : ℝ), (1003398181/2000000000 : ℝ)] ![(8888928039233/20000000000000 : ℝ), (3844830046419/25000000000000 : ℝ), (20088019803847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415179859/10000000000 : ℝ)|^8407 ≤ (8888928039233/20000000000000 : ℝ)^6359
        have hw : |(5415179859/10000000000 : ℝ)|=(5415179859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2426635527/10000000000 : ℝ)|^8407 ≤ (3844830046419/25000000000000 : ℝ)^6359
        have hw : |(-2426635527/10000000000 : ℝ)|=(2426635527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003398181/2000000000 : ℝ)|^8407 ≤ (20088019803847/50000000000000 : ℝ)^6359
        have hw : |(1003398181/2000000000 : ℝ)|=(1003398181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s1_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083035703/2000000000 : ℝ)*x 0 + (1003398353/2000000000 : ℝ)*x 1 + (-121331809/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083035703/2000000000 : ℝ)^8407 ≤ (5555578201599/12500000000000 : ℝ)^6359 := by
    have hnat : (1083035703 : ℕ)^8407*12500000000000^6359 ≤ 5555578201599^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083035703 2000000000 5555578201599 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003398353/2000000000 : ℝ)^8407 ≤ (40176048712579/100000000000000 : ℝ)^6359 := by
    have hnat : (1003398353 : ℕ)^8407*100000000000000^6359 ≤ 40176048712579^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003398353 2000000000 40176048712579 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121331809/500000000 : ℝ)^8407 ≤ (1537932565707/10000000000000 : ℝ)^6359 := by
    have hnat : (121331809 : ℕ)^8407*10000000000000^6359 ≤ 1537932565707^6359*500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121331809 500000000 1537932565707 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083035703/2000000000 : ℝ), (1003398353/2000000000 : ℝ), (-121331809/500000000 : ℝ)] ![(5555578201599/12500000000000 : ℝ), (40176048712579/100000000000000 : ℝ), (1537932565707/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083035703/2000000000 : ℝ)|^8407 ≤ (5555578201599/12500000000000 : ℝ)^6359
        have hw : |(1083035703/2000000000 : ℝ)|=(1083035703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003398353/2000000000 : ℝ)|^8407 ≤ (40176048712579/100000000000000 : ℝ)^6359
        have hw : |(1003398353/2000000000 : ℝ)|=(1003398353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121331809/500000000 : ℝ)|^8407 ≤ (1537932565707/10000000000000 : ℝ)^6359
        have hw : |(-121331809/500000000 : ℝ)|=(121331809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s1_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155640311/5000000000 : ℝ)*x 0 + (3690381341/10000000000 : ℝ)*x 1 + (5033496077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155640311/5000000000 : ℝ)^8407 ≤ (32879591929931/100000000000000 : ℝ)^6359 := by
    have hnat : (2155640311 : ℕ)^8407*100000000000000^6359 ≤ 32879591929931^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155640311 5000000000 32879591929931 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3690381341/10000000000 : ℝ)^8407 ≤ (1338476721911/5000000000000 : ℝ)^6359 := by
    have hnat : (3690381341 : ℕ)^8407*5000000000000^6359 ≤ 1338476721911^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690381341 10000000000 1338476721911 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5033496077/10000000000 : ℝ)^8407 ≤ (20175436811429/50000000000000 : ℝ)^6359 := by
    have hnat : (5033496077 : ℕ)^8407*50000000000000^6359 ≤ 20175436811429^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033496077 10000000000 20175436811429 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155640311/5000000000 : ℝ), (3690381341/10000000000 : ℝ), (5033496077/10000000000 : ℝ)] ![(32879591929931/100000000000000 : ℝ), (1338476721911/5000000000000 : ℝ), (20175436811429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155640311/5000000000 : ℝ)|^8407 ≤ (32879591929931/100000000000000 : ℝ)^6359
        have hw : |(2155640311/5000000000 : ℝ)|=(2155640311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3690381341/10000000000 : ℝ)|^8407 ≤ (1338476721911/5000000000000 : ℝ)^6359
        have hw : |(3690381341/10000000000 : ℝ)|=(3690381341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5033496077/10000000000 : ℝ)|^8407 ≤ (20175436811429/50000000000000 : ℝ)^6359
        have hw : |(5033496077/10000000000 : ℝ)|=(5033496077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s1_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069388689/10000000000 : ℝ)*x 0 + (5025829509/10000000000 : ℝ)*x 1 + (1134735819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069388689/10000000000 : ℝ)^8407 ≤ (12459481427899/100000000000000 : ℝ)^6359 := by
    have hnat : (2069388689 : ℕ)^8407*100000000000000^6359 ≤ 12459481427899^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069388689 10000000000 12459481427899 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5025829509/10000000000 : ℝ)^8407 ≤ (8053928223297/20000000000000 : ℝ)^6359 := by
    have hnat : (5025829509 : ℕ)^8407*20000000000000^6359 ≤ 8053928223297^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025829509 10000000000 8053928223297 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134735819/2000000000 : ℝ)^8407 ≤ (47270877434021/100000000000000 : ℝ)^6359 := by
    have hnat : (1134735819 : ℕ)^8407*100000000000000^6359 ≤ 47270877434021^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134735819 2000000000 47270877434021 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069388689/10000000000 : ℝ), (5025829509/10000000000 : ℝ), (1134735819/2000000000 : ℝ)] ![(12459481427899/100000000000000 : ℝ), (8053928223297/20000000000000 : ℝ), (47270877434021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069388689/10000000000 : ℝ)|^8407 ≤ (12459481427899/100000000000000 : ℝ)^6359
        have hw : |(-2069388689/10000000000 : ℝ)|=(2069388689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5025829509/10000000000 : ℝ)|^8407 ≤ (8053928223297/20000000000000 : ℝ)^6359
        have hw : |(5025829509/10000000000 : ℝ)|=(5025829509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134735819/2000000000 : ℝ)|^8407 ≤ (47270877434021/100000000000000 : ℝ)^6359
        have hw : |(1134735819/2000000000 : ℝ)|=(1134735819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s1_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243905083/10000000000 : ℝ)*x 0 + (-442487861/2500000000 : ℝ)*x 1 + (5673674811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243905083/10000000000 : ℝ)^8407 ≤ (2129785944187/5000000000000 : ℝ)^6359 := by
    have hnat : (5243905083 : ℕ)^8407*5000000000000^6359 ≤ 2129785944187^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243905083 10000000000 2129785944187 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442487861/2500000000 : ℝ)^8407 ≤ (10133450858283/100000000000000 : ℝ)^6359 := by
    have hnat : (442487861 : ℕ)^8407*100000000000000^6359 ≤ 10133450858283^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442487861 2500000000 10133450858283 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673674811/10000000000 : ℝ)^8407 ≤ (9454166049227/20000000000000 : ℝ)^6359 := by
    have hnat : (5673674811 : ℕ)^8407*20000000000000^6359 ≤ 9454166049227^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673674811 10000000000 9454166049227 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243905083/10000000000 : ℝ), (-442487861/2500000000 : ℝ), (5673674811/10000000000 : ℝ)] ![(2129785944187/5000000000000 : ℝ), (10133450858283/100000000000000 : ℝ), (9454166049227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243905083/10000000000 : ℝ)|^8407 ≤ (2129785944187/5000000000000 : ℝ)^6359
        have hw : |(5243905083/10000000000 : ℝ)|=(5243905083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442487861/2500000000 : ℝ)|^8407 ≤ (10133450858283/100000000000000 : ℝ)^6359
        have hw : |(-442487861/2500000000 : ℝ)|=(442487861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673674811/10000000000 : ℝ)|^8407 ≤ (9454166049227/20000000000000 : ℝ)^6359
        have hw : |(5673674811/10000000000 : ℝ)|=(5673674811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s1_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243905239/10000000000 : ℝ)*x 0 + (22694701/40000000 : ℝ)*x 1 + (-1769950583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243905239/10000000000 : ℝ)^8407 ≤ (21297860279511/50000000000000 : ℝ)^6359 := by
    have hnat : (5243905239 : ℕ)^8407*50000000000000^6359 ≤ 21297860279511^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243905239 10000000000 21297860279511 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22694701/40000000 : ℝ)^8407 ≤ (47270835081681/100000000000000 : ℝ)^6359 := by
    have hnat : (22694701 : ℕ)^8407*100000000000000^6359 ≤ 47270835081681^6359*40000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22694701 40000000 47270835081681 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769950583/10000000000 : ℝ)^8407 ≤ (10133444341229/100000000000000 : ℝ)^6359 := by
    have hnat : (1769950583 : ℕ)^8407*100000000000000^6359 ≤ 10133444341229^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769950583 10000000000 10133444341229 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243905239/10000000000 : ℝ), (22694701/40000000 : ℝ), (-1769950583/10000000000 : ℝ)] ![(21297860279511/50000000000000 : ℝ), (47270835081681/100000000000000 : ℝ), (10133444341229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243905239/10000000000 : ℝ)|^8407 ≤ (21297860279511/50000000000000 : ℝ)^6359
        have hw : |(5243905239/10000000000 : ℝ)|=(5243905239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22694701/40000000 : ℝ)|^8407 ≤ (47270835081681/100000000000000 : ℝ)^6359
        have hw : |(22694701/40000000 : ℝ)|=(22694701/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769950583/10000000000 : ℝ)|^8407 ≤ (10133444341229/100000000000000 : ℝ)^6359
        have hw : |(-1769950583/10000000000 : ℝ)|=(1769950583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s1_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2156356679/5000000000 : ℝ)*x 0 + (2507829067/5000000000 : ℝ)*x 1 + (3708562533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156356679/5000000000 : ℝ)^8407 ≤ (16447019200319/50000000000000 : ℝ)^6359 := by
    have hnat : (2156356679 : ℕ)^8407*50000000000000^6359 ≤ 16447019200319^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156356679 5000000000 16447019200319 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507829067/5000000000 : ℝ)^8407 ≤ (40161930063421/100000000000000 : ℝ)^6359 := by
    have hnat : (2507829067 : ℕ)^8407*100000000000000^6359 ≤ 40161930063421^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507829067 5000000000 40161930063421 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3708562533/10000000000 : ℝ)^8407 ≤ (26944031522427/100000000000000 : ℝ)^6359 := by
    have hnat : (3708562533 : ℕ)^8407*100000000000000^6359 ≤ 26944031522427^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3708562533 10000000000 26944031522427 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156356679/5000000000 : ℝ), (2507829067/5000000000 : ℝ), (3708562533/10000000000 : ℝ)] ![(16447019200319/50000000000000 : ℝ), (40161930063421/100000000000000 : ℝ), (26944031522427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156356679/5000000000 : ℝ)|^8407 ≤ (16447019200319/50000000000000 : ℝ)^6359
        have hw : |(2156356679/5000000000 : ℝ)|=(2156356679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507829067/5000000000 : ℝ)|^8407 ≤ (40161930063421/100000000000000 : ℝ)^6359
        have hw : |(2507829067/5000000000 : ℝ)|=(2507829067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3708562533/10000000000 : ℝ)|^8407 ≤ (26944031522427/100000000000000 : ℝ)^6359
        have hw : |(3708562533/10000000000 : ℝ)|=(3708562533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6043/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10059/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (353/50000 : ℝ) ^ (4203/1024 : ℝ) ≤ (9253706461/6250000000000000000 : ℝ) := by
    have hpowers : (353/50000 : ℝ)^4203 ≤ (9253706461/6250000000000000000 : ℝ)^1024 := by
      have hnat : (353 : ℕ)^4203*6250000000000000000^1024 ≤ 9253706461^1024*50000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 50000 9253706461 6250000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/50000 : ℝ)) (X := (9253706461/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27541/100000 : ℝ) ^ (4203/1024 : ℝ) ≤ (251403361077131583/50000000000000000000 : ℝ) := by
    have hpowers : (27541/100000 : ℝ)^4203 ≤ (251403361077131583/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27541 : ℕ)^4203*50000000000000000000^1024 ≤ 251403361077131583^1024*100000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27541 100000 251403361077131583 50000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27541/100000 : ℝ)) (X := (251403361077131583/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000009253706461/3125000000000000000 : ℝ) ≤ (10000000007214501/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (3125000009253706461/3125000000000000000 : ℝ)^1024 ≤ (10000000007214501/10000000000000000 : ℝ)^4203 := by
      have hnat : (3125000009253706461 : ℕ)^1024*10000000000000000^4203 ≤ 10000000007214501^4203*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000009253706461 3125000000000000000 10000000007214501 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000007214501/10000000000000000 : ℝ)) (X := (3125000009253706461/3125000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50251403435106783271/50000000000000000000 : ℝ) ≤ (10012226934576703/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (50251403435106783271/50000000000000000000 : ℝ)^1024 ≤ (10012226934576703/10000000000000000 : ℝ)^4203 := by
      have hnat : (50251403435106783271 : ℕ)^1024*10000000000000000^4203 ≤ 10012226934576703^4203*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50251403435106783271 50000000000000000000 10012226934576703 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012226934576703/10000000000000000 : ℝ)) (X := (50251403435106783271/50000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25251403361077131583/25000000000000000000 : ℝ) ≤ (2004890772387781/2000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (25251403361077131583/25000000000000000000 : ℝ)^1024 ≤ (2004890772387781/2000000000000000 : ℝ)^4203 := by
      have hnat : (25251403361077131583 : ℕ)^1024*2000000000000000^4203 ≤ 2004890772387781^4203*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25251403361077131583 25000000000000000000 2004890772387781 2000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004890772387781/2000000000000000 : ℝ)) (X := (25251403361077131583/25000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9253706461/6250000000000000000 : ℝ) ≤ ((268332735772165705111/268350000000000000000 : ℝ)+2*(6113463681101/1341750000000000 : ℝ)*(353/50000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (268332735772165705111/268350000000000000000 : ℝ)+2*(6113463681101/1341750000000000 : ℝ)*(353/50000 : ℝ)=(10000000007214501/10000000000000000 : ℝ) by norm_num, show 1+2*(9253706461/6250000000000000000 : ℝ)=(3125000009253706461/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(251403361077131583/50000000000000000000 : ℝ)+(9253706461/6250000000000000000 : ℝ) ≤ ((268332735772165705111/268350000000000000000 : ℝ)+(6113463681101/1341750000000000 : ℝ)*((27541/100000 : ℝ)+(353/50000 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (268332735772165705111/268350000000000000000 : ℝ)+(6113463681101/1341750000000000 : ℝ)*((27541/100000 : ℝ)+(353/50000 : ℝ))=(10012226934576703/10000000000000000 : ℝ) by norm_num, show 1+(251403361077131583/50000000000000000000 : ℝ)+(9253706461/6250000000000000000 : ℝ)=(50251403435106783271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(251403361077131583/50000000000000000000 : ℝ) ≤ ((268332735772165705111/268350000000000000000 : ℝ)+2*(6113463681101/1341750000000000 : ℝ)*(27541/100000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (268332735772165705111/268350000000000000000 : ℝ)+2*(6113463681101/1341750000000000 : ℝ)*(27541/100000 : ℝ)=(2004890772387781/2000000000000000 : ℝ) by norm_num, show 1+2*(251403361077131583/50000000000000000000 : ℝ)=(25251403361077131583/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (268332735772165705111/268350000000000000000 : ℝ)*(X 1 0+X 2 0)+(6113463681101/1341750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (353/50000 : ℝ)) (hi := (27541/100000 : ℝ)) (c := (268332735772165705111/268350000000000000000 : ℝ)) (alpha := (6113463681101/1341750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (268332735772165705111/268350000000000000000 : ℝ)*(X 0 1+X 2 1)+(6113463681101/1341750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (353/50000 : ℝ)) (hi := (27541/100000 : ℝ)) (c := (268332735772165705111/268350000000000000000 : ℝ)) (alpha := (6113463681101/1341750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (268332735772165705111/268350000000000000000 : ℝ)*(X 0 2+X 1 2)+(6113463681101/1341750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (353/50000 : ℝ)) (hi := (27541/100000 : ℝ)) (c := (268332735772165705111/268350000000000000000 : ℝ)) (alpha := (6113463681101/1341750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2068681473/10000000000 : ℝ)*X 0 0+(1136537209/2000000000 : ℝ)*X 0 1+(2508495191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415179859/10000000000 : ℝ)*X 1 0+(-2426635527/10000000000 : ℝ)*X 1 1+(1003398181/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083035703/2000000000 : ℝ)*X 2 0+(1003398353/2000000000 : ℝ)*X 2 1+(-121331809/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155640311/5000000000 : ℝ)*X 0 0+(3690381341/10000000000 : ℝ)*X 0 1+(5033496077/10000000000 : ℝ)*X 0 2+(2155640311/5000000000 : ℝ)*X 1 0+(3690381341/10000000000 : ℝ)*X 1 1+(5033496077/10000000000 : ℝ)*X 1 2+(2155640311/5000000000 : ℝ)*X 2 0+(3690381341/10000000000 : ℝ)*X 2 1+(5033496077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2069388689/10000000000 : ℝ)*X 0 0+(5025829509/10000000000 : ℝ)*X 0 1+(1134735819/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243905083/10000000000 : ℝ)*X 1 0+(-442487861/2500000000 : ℝ)*X 1 1+(5673674811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5243905239/10000000000 : ℝ)*X 2 0+(22694701/40000000 : ℝ)*X 2 1+(-1769950583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2156356679/5000000000 : ℝ)*X 0 0+(2507829067/5000000000 : ℝ)*X 0 1+(3708562533/10000000000 : ℝ)*X 0 2+(2156356679/5000000000 : ℝ)*X 1 0+(2507829067/5000000000 : ℝ)*X 1 1+(3708562533/10000000000 : ℝ)*X 1 2+(2156356679/5000000000 : ℝ)*X 2 0+(2507829067/5000000000 : ℝ)*X 2 1+(3708562533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6934352002421196845501666763/1118125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12433729/781250000000 : ℝ)*(base19) + (1183742093/100000000000000 : ℝ)*(base23) + (16424969/50000000000000 : ℝ)*(upper2) + (366883643/100000000000000 : ℝ)*(upper3) + (51771023/100000000000000 : ℝ)*(upper4) + (280844534105711/25000000000000 : ℝ)*(major0) + (280844534105711/25000000000000 : ℝ)*(major1) + (280844534105711/25000000000000 : ℝ)*(major2) + (300439964924729/20000000000000 : ℝ)*(sp0) + (1502205919188391/100000000000000 : ℝ)*(sp1) + (150220632696361/10000000000000 : ℝ)*(sp2) + (372271290242719/50000000000000 : ℝ)*(sp3) + (7686082057/100000000000000 : ℝ)*(sp4) + (1493732233/25000000000000 : ℝ)*(sp7) + (744548555414369/100000000000000 : ℝ)*(f.failure) + (751103755352851/50000000000000 : ℝ)*(f.sum) + (684682600408481/67087500000000000000000000000 : ℝ)*base66 + (23435289700845811079/6708750000000000000000000000000000 : ℝ)*base68 + (43560956059722061079/6708750000000000000000000000000000 : ℝ)*base70 + (89730309731419561079/6708750000000000000000000000000000 : ℝ)*base72 + (177864963566587/134175000000000000000000000000 : ℝ)*base74 + (108221921646409561079/6708750000000000000000000000000000 : ℝ)*base76 + (86302287959078311079/6708750000000000000000000000000000 : ℝ)*base78 + (112930803730350811079/6708750000000000000000000000000000 : ℝ)*base80 + (58309955869931/67087500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (573941/250000000000000000000 : ℝ)*base90 + (573941/250000000000000000000 : ℝ)*base92 + (573941/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (301871226746772245588595373/111812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247911309/100000000000000 : ℝ)*(base19) + (338055243/100000000000000 : ℝ)*(base23) + (157110957/100000000000000 : ℝ)*(lower2) + (24143741/10000000000000 : ℝ)*(lower3) + (22281181/12500000000000 : ℝ)*(lower4) + (57715858092857/5000000000000 : ℝ)*(major0) + (57715858092857/5000000000000 : ℝ)*(major1) + (57715858092857/5000000000000 : ℝ)*(major2) + (2379953933/50000000000000 : ℝ)*(sp0) + (59912691/50000000000000 : ℝ)*(sp2) + (1543575261446603/100000000000000 : ℝ)*(sp4) + (38589494336079/2500000000000 : ℝ)*(sp5) + (385894890868461/25000000000000 : ℝ)*(sp6) + (19126355309163/2500000000000 : ℝ)*(sp7) + (19126355309163/2500000000000 : ℝ)*(f.failure) + (1543580021354469/100000000000000 : ℝ)*(f.sum) + (241305139061831/26835000000000000000000000000 : ℝ)*base65 + (8126460056789142127/1341750000000000000000000000000000 : ℝ)*base67 + (9379932728399142127/1341750000000000000000000000000000 : ℝ)*base69 + (2077474713141107873/1341750000000000000000000000000000 : ℝ)*base72 + (1851739057493/3354375000000000000000000000 : ℝ)*base74 + (9642602211068892127/1341750000000000000000000000000000 : ℝ)*base75 + (7833288984628392127/1341750000000000000000000000000000 : ℝ)*base77 + (2131517926486392127/1341750000000000000000000000000000 : ℝ)*base79 + (44158940105219/6708750000000000000000000000 : ℝ)*base81 + (13207/6250000000000000000 : ℝ)*base90 + (13207/6250000000000000000 : ℝ)*base92 + (13207/6250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1214_s2_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-423627947/2000000000 : ℝ)*x 0 + (1374406993/2500000000 : ℝ)*x 1 + (1292633079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423627947/2000000000 : ℝ)^8407 ≤ (12849001491233/100000000000000 : ℝ)^6359 := by
    have hnat : (423627947 : ℕ)^8407*100000000000000^6359 ≤ 12849001491233^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423627947 2000000000 12849001491233 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374406993/2500000000 : ℝ)^8407 ≤ (22670723924267/50000000000000 : ℝ)^6359 := by
    have hnat : (1374406993 : ℕ)^8407*50000000000000^6359 ≤ 22670723924267^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374406993 2500000000 22670723924267 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292633079/2500000000 : ℝ)^8407 ≤ (20904775323461/50000000000000 : ℝ)^6359 := by
    have hnat : (1292633079 : ℕ)^8407*50000000000000^6359 ≤ 20904775323461^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292633079 2500000000 20904775323461 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423627947/2000000000 : ℝ), (1374406993/2500000000 : ℝ), (1292633079/2500000000 : ℝ)] ![(12849001491233/100000000000000 : ℝ), (22670723924267/50000000000000 : ℝ), (20904775323461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423627947/2000000000 : ℝ)|^8407 ≤ (12849001491233/100000000000000 : ℝ)^6359
        have hw : |(-423627947/2000000000 : ℝ)|=(423627947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374406993/2500000000 : ℝ)|^8407 ≤ (22670723924267/50000000000000 : ℝ)^6359
        have hw : |(1374406993/2500000000 : ℝ)|=(1374406993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1292633079/2500000000 : ℝ)|^8407 ≤ (20904775323461/50000000000000 : ℝ)^6359
        have hw : |(1292633079/2500000000 : ℝ)|=(1292633079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s2_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685413987/5000000000 : ℝ)*x 0 + (-2287736103/10000000000 : ℝ)*x 1 + (5170537189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685413987/5000000000 : ℝ)^8407 ≤ (5495503251801/12500000000000 : ℝ)^6359 := by
    have hnat : (2685413987 : ℕ)^8407*12500000000000^6359 ≤ 5495503251801^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685413987 5000000000 5495503251801 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287736103/10000000000 : ℝ)^8407 ≤ (889148202001/6250000000000 : ℝ)^6359 := by
    have hnat : (2287736103 : ℕ)^8407*6250000000000^6359 ≤ 889148202001^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287736103 10000000000 889148202001 6250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170537189/10000000000 : ℝ)^8407 ≤ (41809602741071/100000000000000 : ℝ)^6359 := by
    have hnat : (5170537189 : ℕ)^8407*100000000000000^6359 ≤ 41809602741071^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170537189 10000000000 41809602741071 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685413987/5000000000 : ℝ), (-2287736103/10000000000 : ℝ), (5170537189/10000000000 : ℝ)] ![(5495503251801/12500000000000 : ℝ), (889148202001/6250000000000 : ℝ), (41809602741071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685413987/5000000000 : ℝ)|^8407 ≤ (5495503251801/12500000000000 : ℝ)^6359
        have hw : |(2685413987/5000000000 : ℝ)|=(2685413987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2287736103/10000000000 : ℝ)|^8407 ≤ (889148202001/6250000000000 : ℝ)^6359
        have hw : |(-2287736103/10000000000 : ℝ)|=(2287736103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170537189/10000000000 : ℝ)|^8407 ≤ (41809602741071/100000000000000 : ℝ)^6359
        have hw : |(5170537189/10000000000 : ℝ)|=(5170537189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s2_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33567689/62500000 : ℝ)*x 0 + (5170534061/10000000000 : ℝ)*x 1 + (-571934297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33567689/62500000 : ℝ)^8407 ≤ (43964050537113/100000000000000 : ℝ)^6359 := by
    have hnat : (33567689 : ℕ)^8407*100000000000000^6359 ≤ 43964050537113^6359*62500000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33567689 62500000 43964050537113 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5170534061/10000000000 : ℝ)^8407 ≤ (41809569301607/100000000000000 : ℝ)^6359 := by
    have hnat : (5170534061 : ℕ)^8407*100000000000000^6359 ≤ 41809569301607^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170534061 10000000000 41809569301607 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571934297/2500000000 : ℝ)^8407 ≤ (7113190076063/50000000000000 : ℝ)^6359 := by
    have hnat : (571934297 : ℕ)^8407*50000000000000^6359 ≤ 7113190076063^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571934297 2500000000 7113190076063 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33567689/62500000 : ℝ), (5170534061/10000000000 : ℝ), (-571934297/2500000000 : ℝ)] ![(43964050537113/100000000000000 : ℝ), (41809569301607/100000000000000 : ℝ), (7113190076063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33567689/62500000 : ℝ)|^8407 ≤ (43964050537113/100000000000000 : ℝ)^6359
        have hw : |(33567689/62500000 : ℝ)|=(33567689/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5170534061/10000000000 : ℝ)|^8407 ≤ (41809569301607/100000000000000 : ℝ)^6359
        have hw : |(5170534061/10000000000 : ℝ)|=(5170534061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571934297/2500000000 : ℝ)|^8407 ≤ (7113190076063/50000000000000 : ℝ)^6359
        have hw : |(-571934297/2500000000 : ℝ)|=(571934297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s2_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345380739/10000000000 : ℝ)*x 0 + (4027618589/10000000000 : ℝ)*x 1 + (585945893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345380739/10000000000 : ℝ)^8407 ≤ (33223846754047/100000000000000 : ℝ)^6359 := by
    have hnat : (4345380739 : ℕ)^8407*100000000000000^6359 ≤ 33223846754047^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345380739 10000000000 33223846754047 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027618589/10000000000 : ℝ)^8407 ≤ (30050308381407/100000000000000 : ℝ)^6359 := by
    have hnat : (4027618589 : ℕ)^8407*100000000000000^6359 ≤ 30050308381407^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027618589 10000000000 30050308381407 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585945893/1250000000 : ℝ)^8407 ≤ (9181461212187/25000000000000 : ℝ)^6359 := by
    have hnat : (585945893 : ℕ)^8407*25000000000000^6359 ≤ 9181461212187^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585945893 1250000000 9181461212187 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345380739/10000000000 : ℝ), (4027618589/10000000000 : ℝ), (585945893/1250000000 : ℝ)] ![(33223846754047/100000000000000 : ℝ), (30050308381407/100000000000000 : ℝ), (9181461212187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345380739/10000000000 : ℝ)|^8407 ≤ (33223846754047/100000000000000 : ℝ)^6359
        have hw : |(4345380739/10000000000 : ℝ)|=(4345380739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027618589/10000000000 : ℝ)|^8407 ≤ (30050308381407/100000000000000 : ℝ)^6359
        have hw : |(4027618589/10000000000 : ℝ)|=(4027618589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(585945893/1250000000 : ℝ)|^8407 ≤ (9181461212187/25000000000000 : ℝ)^6359
        have hw : |(585945893/1250000000 : ℝ)|=(585945893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s2_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529555689/2500000000 : ℝ)*x 0 + (5172678137/10000000000 : ℝ)*x 1 + (1099092557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529555689/2500000000 : ℝ)^8407 ≤ (12849667312551/100000000000000 : ℝ)^6359 := by
    have hnat : (529555689 : ℕ)^8407*100000000000000^6359 ≤ 12849667312551^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529555689 2500000000 12849667312551 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172678137/10000000000 : ℝ)^8407 ≤ (41832491785949/100000000000000 : ℝ)^6359 := by
    have hnat : (5172678137 : ℕ)^8407*100000000000000^6359 ≤ 41832491785949^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172678137 10000000000 41832491785949 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099092557/2000000000 : ℝ)^8407 ≤ (45317840885327/100000000000000 : ℝ)^6359 := by
    have hnat : (1099092557 : ℕ)^8407*100000000000000^6359 ≤ 45317840885327^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099092557 2000000000 45317840885327 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529555689/2500000000 : ℝ), (5172678137/10000000000 : ℝ), (1099092557/2000000000 : ℝ)] ![(12849667312551/100000000000000 : ℝ), (41832491785949/100000000000000 : ℝ), (45317840885327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529555689/2500000000 : ℝ)|^8407 ≤ (12849667312551/100000000000000 : ℝ)^6359
        have hw : |(-529555689/2500000000 : ℝ)|=(529555689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172678137/10000000000 : ℝ)|^8407 ≤ (41832491785949/100000000000000 : ℝ)^6359
        have hw : |(5172678137/10000000000 : ℝ)|=(5172678137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099092557/2000000000 : ℝ)|^8407 ≤ (45317840885327/100000000000000 : ℝ)^6359
        have hw : |(1099092557/2000000000 : ℝ)|=(1099092557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s2_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330465371/625000000 : ℝ)*x 0 + (-122675551/625000000 : ℝ)*x 1 + (1099092563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330465371/625000000 : ℝ)^8407 ≤ (43063927599793/100000000000000 : ℝ)^6359 := by
    have hnat : (330465371 : ℕ)^8407*100000000000000^6359 ≤ 43063927599793^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330465371 625000000 43063927599793 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122675551/625000000 : ℝ)^8407 ≤ (5809115585089/50000000000000 : ℝ)^6359 := by
    have hnat : (122675551 : ℕ)^8407*50000000000000^6359 ≤ 5809115585089^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122675551 625000000 5809115585089 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099092563/2000000000 : ℝ)^8407 ≤ (9063568242479/20000000000000 : ℝ)^6359 := by
    have hnat : (1099092563 : ℕ)^8407*20000000000000^6359 ≤ 9063568242479^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099092563 2000000000 9063568242479 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330465371/625000000 : ℝ), (-122675551/625000000 : ℝ), (1099092563/2000000000 : ℝ)] ![(43063927599793/100000000000000 : ℝ), (5809115585089/50000000000000 : ℝ), (9063568242479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330465371/625000000 : ℝ)|^8407 ≤ (43063927599793/100000000000000 : ℝ)^6359
        have hw : |(330465371/625000000 : ℝ)|=(330465371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122675551/625000000 : ℝ)|^8407 ≤ (5809115585089/50000000000000 : ℝ)^6359
        have hw : |(-122675551/625000000 : ℝ)|=(122675551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099092563/2000000000 : ℝ)|^8407 ≤ (9063568242479/20000000000000 : ℝ)^6359
        have hw : |(1099092563/2000000000 : ℝ)|=(1099092563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s2_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287446117/10000000000 : ℝ)*x 0 + (1373865713/2500000000 : ℝ)*x 1 + (-490702129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287446117/10000000000 : ℝ)^8407 ≤ (43063929548733/100000000000000 : ℝ)^6359 := by
    have hnat : (5287446117 : ℕ)^8407*100000000000000^6359 ≤ 43063929548733^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287446117 10000000000 43063929548733 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373865713/2500000000 : ℝ)^8407 ≤ (45317841615779/100000000000000 : ℝ)^6359 := by
    have hnat : (1373865713 : ℕ)^8407*100000000000000^6359 ≤ 45317841615779^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373865713 2500000000 45317841615779 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490702129/2500000000 : ℝ)^8407 ≤ (2904557205629/25000000000000 : ℝ)^6359 := by
    have hnat : (490702129 : ℕ)^8407*25000000000000^6359 ≤ 2904557205629^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490702129 2500000000 2904557205629 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287446117/10000000000 : ℝ), (1373865713/2500000000 : ℝ), (-490702129/2500000000 : ℝ)] ![(43063929548733/100000000000000 : ℝ), (45317841615779/100000000000000 : ℝ), (2904557205629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287446117/10000000000 : ℝ)|^8407 ≤ (43063929548733/100000000000000 : ℝ)^6359
        have hw : |(5287446117/10000000000 : ℝ)|=(5287446117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373865713/2500000000 : ℝ)|^8407 ≤ (45317841615779/100000000000000 : ℝ)^6359
        have hw : |(1373865713/2500000000 : ℝ)|=(1373865713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490702129/2500000000 : ℝ)|^8407 ≤ (2904557205629/25000000000000 : ℝ)^6359
        have hw : |(-490702129/2500000000 : ℝ)|=(490702129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s2_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345550743/10000000000 : ℝ)*x 0 + (936648061/2000000000 : ℝ)*x 1 + (2015993239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345550743/10000000000 : ℝ)^8407 ≤ (3322556520119/10000000000000 : ℝ)^6359 := by
    have hnat : (4345550743 : ℕ)^8407*10000000000000^6359 ≤ 3322556520119^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345550743 10000000000 3322556520119 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936648061/2000000000 : ℝ)^8407 ≤ (36681034050537/100000000000000 : ℝ)^6359 := by
    have hnat : (936648061 : ℕ)^8407*100000000000000^6359 ≤ 36681034050537^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936648061 2000000000 36681034050537 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015993239/5000000000 : ℝ)^8407 ≤ (15046700368283/50000000000000 : ℝ)^6359 := by
    have hnat : (2015993239 : ℕ)^8407*50000000000000^6359 ≤ 15046700368283^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015993239 5000000000 15046700368283 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345550743/10000000000 : ℝ), (936648061/2000000000 : ℝ), (2015993239/5000000000 : ℝ)] ![(3322556520119/10000000000000 : ℝ), (36681034050537/100000000000000 : ℝ), (15046700368283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345550743/10000000000 : ℝ)|^8407 ≤ (3322556520119/10000000000000 : ℝ)^6359
        have hw : |(4345550743/10000000000 : ℝ)|=(4345550743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936648061/2000000000 : ℝ)|^8407 ≤ (36681034050537/100000000000000 : ℝ)^6359
        have hw : |(936648061/2000000000 : ℝ)|=(936648061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015993239/5000000000 : ℝ)|^8407 ≤ (15046700368283/50000000000000 : ℝ)^6359
        have hw : |(2015993239/5000000000 : ℝ)|=(2015993239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1173/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16297/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6043/100000 : ℝ) ^ (4203/1024 : ℝ) ≤ (198925652017879/20000000000000000000 : ℝ) := by
    have hpowers : (6043/100000 : ℝ)^4203 ≤ (198925652017879/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6043 : ℕ)^4203*20000000000000000000^1024 ≤ 198925652017879^1024*100000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6043 100000 198925652017879 20000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6043/100000 : ℝ)) (X := (198925652017879/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10059/50000 : ℝ) ^ (4203/1024 : ℝ) ≤ (138538113028509053/100000000000000000000 : ℝ) := by
    have hpowers : (10059/50000 : ℝ)^4203 ≤ (138538113028509053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10059 : ℕ)^4203*100000000000000000000^1024 ≤ 138538113028509053^1024*50000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10059 50000 138538113028509053 100000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10059/50000 : ℝ)) (X := (138538113028509053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000198925652017879/10000000000000000000 : ℝ) ≤ (1250006058123223/1250000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (10000198925652017879/10000000000000000000 : ℝ)^1024 ≤ (1250006058123223/1250000000000000 : ℝ)^4203 := by
      have hnat : (10000198925652017879 : ℕ)^1024*1250000000000000^4203 ≤ 1250006058123223^4203*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000198925652017879 10000000000000000000 1250006058123223 1250000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250006058123223/1250000000000000 : ℝ)) (X := (10000198925652017879/10000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6258720796330537403/6250000000000000000 : ℝ) ≤ (10003397720479089/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (6258720796330537403/6250000000000000000 : ℝ)^1024 ≤ (10003397720479089/10000000000000000 : ℝ)^4203 := by
      have hnat : (6258720796330537403 : ℕ)^1024*10000000000000000^4203 ≤ 10003397720479089^4203*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6258720796330537403 6250000000000000000 10003397720479089 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003397720479089/10000000000000000 : ℝ)) (X := (6258720796330537403/6250000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50138538113028509053/50000000000000000000 : ℝ) ≤ (5003373487986197/5000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (50138538113028509053/50000000000000000000 : ℝ)^1024 ≤ (5003373487986197/5000000000000000 : ℝ)^4203 := by
      have hnat : (50138538113028509053 : ℕ)^1024*5000000000000000^4203 ≤ 5003373487986197^4203*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50138538113028509053 50000000000000000000 5003373487986197 5000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003373487986197/5000000000000000 : ℝ)) (X := (50138538113028509053/50000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(198925652017879/20000000000000000000 : ℝ) ≤ ((14071020304278282557/14075000000000000000 : ℝ)+2*(669851098661/281500000000000 : ℝ)*(6043/100000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (14071020304278282557/14075000000000000000 : ℝ)+2*(669851098661/281500000000000 : ℝ)*(6043/100000 : ℝ)=(1250006058123223/1250000000000000 : ℝ) by norm_num, show 1+2*(198925652017879/20000000000000000000 : ℝ)=(10000198925652017879/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(138538113028509053/100000000000000000000 : ℝ)+(198925652017879/20000000000000000000 : ℝ) ≤ ((14071020304278282557/14075000000000000000 : ℝ)+(669851098661/281500000000000 : ℝ)*((10059/50000 : ℝ)+(6043/100000 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (14071020304278282557/14075000000000000000 : ℝ)+(669851098661/281500000000000 : ℝ)*((10059/50000 : ℝ)+(6043/100000 : ℝ))=(10003397720479089/10000000000000000 : ℝ) by norm_num, show 1+(138538113028509053/100000000000000000000 : ℝ)+(198925652017879/20000000000000000000 : ℝ)=(6258720796330537403/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(138538113028509053/100000000000000000000 : ℝ) ≤ ((14071020304278282557/14075000000000000000 : ℝ)+2*(669851098661/281500000000000 : ℝ)*(10059/50000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (14071020304278282557/14075000000000000000 : ℝ)+2*(669851098661/281500000000000 : ℝ)*(10059/50000 : ℝ)=(5003373487986197/5000000000000000 : ℝ) by norm_num, show 1+2*(138538113028509053/100000000000000000000 : ℝ)=(50138538113028509053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14071020304278282557/14075000000000000000 : ℝ)*(X 1 0+X 2 0)+(669851098661/281500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (6043/100000 : ℝ)) (hi := (10059/50000 : ℝ)) (c := (14071020304278282557/14075000000000000000 : ℝ)) (alpha := (669851098661/281500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14071020304278282557/14075000000000000000 : ℝ)*(X 0 1+X 2 1)+(669851098661/281500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (6043/100000 : ℝ)) (hi := (10059/50000 : ℝ)) (c := (14071020304278282557/14075000000000000000 : ℝ)) (alpha := (669851098661/281500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14071020304278282557/14075000000000000000 : ℝ)*(X 0 2+X 1 2)+(669851098661/281500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (6043/100000 : ℝ)) (hi := (10059/50000 : ℝ)) (c := (14071020304278282557/14075000000000000000 : ℝ)) (alpha := (669851098661/281500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423627947/2000000000 : ℝ)*X 0 0+(1374406993/2500000000 : ℝ)*X 0 1+(1292633079/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685413987/5000000000 : ℝ)*X 1 0+(-2287736103/10000000000 : ℝ)*X 1 1+(5170537189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((33567689/62500000 : ℝ)*X 2 0+(5170534061/10000000000 : ℝ)*X 2 1+(-571934297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345380739/10000000000 : ℝ)*X 0 0+(4027618589/10000000000 : ℝ)*X 0 1+(585945893/1250000000 : ℝ)*X 0 2+(4345380739/10000000000 : ℝ)*X 1 0+(4027618589/10000000000 : ℝ)*X 1 1+(585945893/1250000000 : ℝ)*X 1 2+(4345380739/10000000000 : ℝ)*X 2 0+(4027618589/10000000000 : ℝ)*X 2 1+(585945893/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529555689/2500000000 : ℝ)*X 0 0+(5172678137/10000000000 : ℝ)*X 0 1+(1099092557/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330465371/625000000 : ℝ)*X 1 0+(-122675551/625000000 : ℝ)*X 1 1+(1099092563/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287446117/10000000000 : ℝ)*X 2 0+(1373865713/2500000000 : ℝ)*X 2 1+(-490702129/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345550743/10000000000 : ℝ)*X 0 0+(936648061/2000000000 : ℝ)*X 0 1+(2015993239/5000000000 : ℝ)*X 0 2+(4345550743/10000000000 : ℝ)*X 1 0+(936648061/2000000000 : ℝ)*X 1 1+(2015993239/5000000000 : ℝ)*X 1 2+(4345550743/10000000000 : ℝ)*X 2 0+(936648061/2000000000 : ℝ)*X 2 1+(2015993239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (915690537482766639997518633/351875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (408102121/50000000000000 : ℝ)*(base19) + (231572739/12500000000000 : ℝ)*(base23) + (5919689/4000000000000 : ℝ)*(upper2) + (654756253/100000000000000 : ℝ)*(upper3) + (284153307/100000000000000 : ℝ)*(upper4) + (2286297574103223/100000000000000 : ℝ)*(major0) + (2286297574103223/100000000000000 : ℝ)*(major1) + (2286297574103223/100000000000000 : ℝ)*(major2) + (1528626538493873/50000000000000 : ℝ)*(sp0) + (1528645045891019/50000000000000 : ℝ)*(sp1) + (191080565962773/6250000000000 : ℝ)*(sp2) + (47352578226409/3125000000000 : ℝ)*(sp3) + (37830998533/100000000000000 : ℝ)*(sp4) + (433004623/2000000000000 : ℝ)*(sp7) + (757652076738119/50000000000000 : ℝ)*(f.failure) + (76432272699657/2500000000000 : ℝ)*(f.sum) + (87309374568397/14075000000000000000000000000 : ℝ)*base66 + (1229432344236031211/1407500000000000000000000000000000 : ℝ)*base67 + (830059373948968789/1407500000000000000000000000000000 : ℝ)*base70 + (9608444019706468789/1407500000000000000000000000000000 : ℝ)*base72 + (15200664542697/14075000000000000000000000000 : ℝ)*base74 + (10177431609156468789/1407500000000000000000000000000000 : ℝ)*base76 + (6626454430716468789/1407500000000000000000000000000000 : ℝ)*base78 + (7825260504126468789/1407500000000000000000000000000000 : ℝ)*base80 + (66611256136697/14075000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (237309/125000000000000000000 : ℝ)*base89 + (237309/125000000000000000000 : ℝ)*base91 + (237309/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (469674617786327693817406779/351875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (602477599/100000000000000 : ℝ)*(base19) + (182886427/20000000000000 : ℝ)*(base23) + (63263471/100000000000000 : ℝ)*(upper2) + (13048487/12500000000000 : ℝ)*(upper3) + (26773523/100000000000000 : ℝ)*(upper5) + (1158384913299017/50000000000000 : ℝ)*(major0) + (1158384913299017/50000000000000 : ℝ)*(major1) + (1158384913299017/50000000000000 : ℝ)*(major2) + (2712843829/50000000000000 : ℝ)*(sp1) + (2178995191/20000000000000 : ℝ)*(sp2) + (1549019582189739/50000000000000 : ℝ)*(sp4) + (3098033136214221/100000000000000 : ℝ)*(sp5) + (3098027354971387/100000000000000 : ℝ)*(sp6) + (767750222162009/50000000000000 : ℝ)*(sp7) + (767750222162009/50000000000000 : ℝ)*(f.failure) + (1549019582189739/50000000000000 : ℝ)*(f.sum) + (3869827093997/1759375000000000000000000000 : ℝ)*base66 + (5701987406958196469/703750000000000000000000000000000 : ℝ)*base67 + (3342076593140696469/703750000000000000000000000000000 : ℝ)*base69 + (4921649599210696469/703750000000000000000000000000000 : ℝ)*base71 + (3578154541987/7037500000000000000000000000 : ℝ)*base73 + (526880073064446469/703750000000000000000000000000000 : ℝ)*base75 + (1401961689769446469/703750000000000000000000000000000 : ℝ)*base77 + (13539759187509446469/703750000000000000000000000000000 : ℝ)*base79 + (35421742126713/7037500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (769901/125000000000000000000 : ℝ)*base90 + (769901/125000000000000000000 : ℝ)*base92 + (769901/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1173/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1214_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1173/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1214_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1214_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1214_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1173/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
