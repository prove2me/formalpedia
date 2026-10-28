-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:50.84199+00:00
-- url     : https://prove2.me/submissions/1dbbb418-e28a-4705-898c-0c78d241c9b1

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
theorem support_rectangle_w1230_s3_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-265319151/1250000000 : ℝ)*x 0 + (5420726393/10000000000 : ℝ)*x 1 + (5239678429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265319151/1250000000 : ℝ)^8423 ≤ (12900561305249/100000000000000 : ℝ)^6375 := by
    have hnat : (265319151 : ℕ)^8423*100000000000000^6375 ≤ 12900561305249^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265319151 1250000000 12900561305249 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420726393/10000000000 : ℝ)^8423 ≤ (5565858540191/12500000000000 : ℝ)^6375 := by
    have hnat : (5420726393 : ℕ)^8423*12500000000000^6375 ≤ 5565858540191^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420726393 10000000000 5565858540191 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239678429/10000000000 : ℝ)^8423 ≤ (10643142590227/25000000000000 : ℝ)^6375 := by
    have hnat : (5239678429 : ℕ)^8423*25000000000000^6375 ≤ 10643142590227^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239678429 10000000000 10643142590227 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265319151/1250000000 : ℝ), (5420726393/10000000000 : ℝ), (5239678429/10000000000 : ℝ)] ![(12900561305249/100000000000000 : ℝ), (5565858540191/12500000000000 : ℝ), (10643142590227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265319151/1250000000 : ℝ)|^8423 ≤ (12900561305249/100000000000000 : ℝ)^6375
        have hw : |(-265319151/1250000000 : ℝ)|=(265319151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420726393/10000000000 : ℝ)|^8423 ≤ (5565858540191/12500000000000 : ℝ)^6375
        have hw : |(5420726393/10000000000 : ℝ)|=(5420726393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239678429/10000000000 : ℝ)|^8423 ≤ (10643142590227/25000000000000 : ℝ)^6375
        have hw : |(5239678429/10000000000 : ℝ)|=(5239678429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s3_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070351513/2000000000 : ℝ)*x 0 + (-442986683/2000000000 : ℝ)*x 1 + (5239678601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070351513/2000000000 : ℝ)^8423 ≤ (43779881265949/100000000000000 : ℝ)^6375 := by
    have hnat : (1070351513 : ℕ)^8423*100000000000000^6375 ≤ 43779881265949^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070351513 2000000000 43779881265949 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442986683/2000000000 : ℝ)^8423 ≤ (6823773253051/50000000000000 : ℝ)^6375 := by
    have hnat : (442986683 : ℕ)^8423*50000000000000^6375 ≤ 6823773253051^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442986683 2000000000 6823773253051 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239678601/10000000000 : ℝ)^8423 ≤ (4257257220737/10000000000000 : ℝ)^6375 := by
    have hnat : (5239678601 : ℕ)^8423*10000000000000^6375 ≤ 4257257220737^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239678601 10000000000 4257257220737 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070351513/2000000000 : ℝ), (-442986683/2000000000 : ℝ), (5239678601/10000000000 : ℝ)] ![(43779881265949/100000000000000 : ℝ), (6823773253051/50000000000000 : ℝ), (4257257220737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070351513/2000000000 : ℝ)|^8423 ≤ (43779881265949/100000000000000 : ℝ)^6375
        have hw : |(1070351513/2000000000 : ℝ)|=(1070351513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442986683/2000000000 : ℝ)|^8423 ≤ (6823773253051/50000000000000 : ℝ)^6375
        have hw : |(-442986683/2000000000 : ℝ)|=(442986683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239678601/10000000000 : ℝ)|^8423 ≤ (4257257220737/10000000000000 : ℝ)^6375
        have hw : |(5239678601/10000000000 : ℝ)|=(5239678601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s3_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351757449/10000000000 : ℝ)*x 0 + (163739969/312500000 : ℝ)*x 1 + (-2214933033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351757449/10000000000 : ℝ)^8423 ≤ (8755976002433/20000000000000 : ℝ)^6375 := by
    have hnat : (5351757449 : ℕ)^8423*20000000000000^6375 ≤ 8755976002433^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351757449 10000000000 8755976002433 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163739969/312500000 : ℝ)^8423 ≤ (42572576576613/100000000000000 : ℝ)^6375 := by
    have hnat : (163739969 : ℕ)^8423*100000000000000^6375 ≤ 42572576576613^6375*312500000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163739969 312500000 42572576576613 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214933033/10000000000 : ℝ)^8423 ≤ (13647543396221/100000000000000 : ℝ)^6375 := by
    have hnat : (2214933033 : ℕ)^8423*100000000000000^6375 ≤ 13647543396221^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214933033 10000000000 13647543396221 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351757449/10000000000 : ℝ), (163739969/312500000 : ℝ), (-2214933033/10000000000 : ℝ)] ![(8755976002433/20000000000000 : ℝ), (42572576576613/100000000000000 : ℝ), (13647543396221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351757449/10000000000 : ℝ)|^8423 ≤ (8755976002433/20000000000000 : ℝ)^6375
        have hw : |(5351757449/10000000000 : ℝ)|=(5351757449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163739969/312500000 : ℝ)|^8423 ≤ (42572576576613/100000000000000 : ℝ)^6375
        have hw : |(163739969/312500000 : ℝ)|=(163739969/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214933033/10000000000 : ℝ)|^8423 ≤ (13647543396221/100000000000000 : ℝ)^6375
        have hw : |(-2214933033/10000000000 : ℝ)|=(2214933033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s3_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87013269/200000000 : ℝ)*x 0 + (4171212083/10000000000 : ℝ)*x 1 + (1134407161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87013269/200000000 : ℝ)^8423 ≤ (33299649971293/100000000000000 : ℝ)^6375 := by
    have hnat : (87013269 : ℕ)^8423*100000000000000^6375 ≤ 33299649971293^6375*200000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87013269 200000000 33299649971293 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171212083/10000000000 : ℝ)^8423 ≤ (31497034435533/100000000000000 : ℝ)^6375 := by
    have hnat : (4171212083 : ℕ)^8423*100000000000000^6375 ≤ 31497034435533^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171212083 10000000000 31497034435533 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134407161/2500000000 : ℝ)^8423 ≤ (17601657789659/50000000000000 : ℝ)^6375 := by
    have hnat : (1134407161 : ℕ)^8423*50000000000000^6375 ≤ 17601657789659^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134407161 2500000000 17601657789659 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87013269/200000000 : ℝ), (4171212083/10000000000 : ℝ), (1134407161/2500000000 : ℝ)] ![(33299649971293/100000000000000 : ℝ), (31497034435533/100000000000000 : ℝ), (17601657789659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87013269/200000000 : ℝ)|^8423 ≤ (33299649971293/100000000000000 : ℝ)^6375
        have hw : |(87013269/200000000 : ℝ)|=(87013269/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171212083/10000000000 : ℝ)|^8423 ≤ (31497034435533/100000000000000 : ℝ)^6375
        have hw : |(4171212083/10000000000 : ℝ)|=(4171212083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134407161/2500000000 : ℝ)|^8423 ≤ (17601657789659/50000000000000 : ℝ)^6375
        have hw : |(1134407161/2500000000 : ℝ)|=(1134407161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s3_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122567793/10000000000 : ℝ)*x 0 + (2620170727/5000000000 : ℝ)*x 1 + (1084011949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122567793/10000000000 : ℝ)^8423 ≤ (2580135685723/20000000000000 : ℝ)^6375 := by
    have hnat : (2122567793 : ℕ)^8423*20000000000000^6375 ≤ 2580135685723^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122567793 10000000000 2580135685723 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620170727/5000000000 : ℝ)^8423 ≤ (42579688239573/100000000000000 : ℝ)^6375 := by
    have hnat : (2620170727 : ℕ)^8423*100000000000000^6375 ≤ 42579688239573^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620170727 5000000000 42579688239573 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084011949/2000000000 : ℝ)^8423 ≤ (44519633309179/100000000000000 : ℝ)^6375 := by
    have hnat : (1084011949 : ℕ)^8423*100000000000000^6375 ≤ 44519633309179^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084011949 2000000000 44519633309179 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122567793/10000000000 : ℝ), (2620170727/5000000000 : ℝ), (1084011949/2000000000 : ℝ)] ![(2580135685723/20000000000000 : ℝ), (42579688239573/100000000000000 : ℝ), (44519633309179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122567793/10000000000 : ℝ)|^8423 ≤ (2580135685723/20000000000000 : ℝ)^6375
        have hw : |(-2122567793/10000000000 : ℝ)|=(2122567793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620170727/5000000000 : ℝ)|^8423 ≤ (42579688239573/100000000000000 : ℝ)^6375
        have hw : |(2620170727/5000000000 : ℝ)|=(2620170727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084011949/2000000000 : ℝ)|^8423 ≤ (44519633309179/100000000000000 : ℝ)^6375
        have hw : |(1084011949/2000000000 : ℝ)|=(1084011949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s3_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652802783/5000000000 : ℝ)*x 0 + (-1017275911/5000000000 : ℝ)*x 1 + (338753729/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652802783/5000000000 : ℝ)^8423 ≤ (43281740490397/100000000000000 : ℝ)^6375 := by
    have hnat : (2652802783 : ℕ)^8423*100000000000000^6375 ≤ 43281740490397^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652802783 5000000000 43281740490397 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017275911/5000000000 : ℝ)^8423 ≤ (6099313532497/50000000000000 : ℝ)^6375 := by
    have hnat : (1017275911 : ℕ)^8423*50000000000000^6375 ≤ 6099313532497^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017275911 5000000000 6099313532497 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338753729/625000000 : ℝ)^8423 ≤ (44519632430117/100000000000000 : ℝ)^6375 := by
    have hnat : (338753729 : ℕ)^8423*100000000000000^6375 ≤ 44519632430117^6375*625000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338753729 625000000 44519632430117 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652802783/5000000000 : ℝ), (-1017275911/5000000000 : ℝ), (338753729/625000000 : ℝ)] ![(43281740490397/100000000000000 : ℝ), (6099313532497/50000000000000 : ℝ), (44519632430117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652802783/5000000000 : ℝ)|^8423 ≤ (43281740490397/100000000000000 : ℝ)^6375
        have hw : |(2652802783/5000000000 : ℝ)|=(2652802783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017275911/5000000000 : ℝ)|^8423 ≤ (6099313532497/50000000000000 : ℝ)^6375
        have hw : |(-1017275911/5000000000 : ℝ)|=(1017275911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338753729/625000000 : ℝ)|^8423 ≤ (44519632430117/100000000000000 : ℝ)^6375
        have hw : |(338753729/625000000 : ℝ)|=(338753729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s3_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652802199/5000000000 : ℝ)*x 0 + (2710030071/5000000000 : ℝ)*x 1 + (-508638189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652802199/5000000000 : ℝ)^8423 ≤ (43281727901167/100000000000000 : ℝ)^6375 := by
    have hnat : (2652802199 : ℕ)^8423*100000000000000^6375 ≤ 43281727901167^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652802199 5000000000 43281727901167 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710030071/5000000000 : ℝ)^8423 ≤ (43476208611/97656250000 : ℝ)^6375 := by
    have hnat : (2710030071 : ℕ)^8423*97656250000^6375 ≤ 43476208611^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710030071 5000000000 43476208611 97656250000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508638189/2500000000 : ℝ)^8423 ≤ (304965861601/2500000000000 : ℝ)^6375 := by
    have hnat : (508638189 : ℕ)^8423*2500000000000^6375 ≤ 304965861601^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508638189 2500000000 304965861601 2500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652802199/5000000000 : ℝ), (2710030071/5000000000 : ℝ), (-508638189/2500000000 : ℝ)] ![(43281727901167/100000000000000 : ℝ), (43476208611/97656250000 : ℝ), (304965861601/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652802199/5000000000 : ℝ)|^8423 ≤ (43281727901167/100000000000000 : ℝ)^6375
        have hw : |(2652802199/5000000000 : ℝ)|=(2652802199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710030071/5000000000 : ℝ)|^8423 ≤ (43476208611/97656250000 : ℝ)^6375
        have hw : |(2710030071/5000000000 : ℝ)|=(2710030071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508638189/2500000000 : ℝ)|^8423 ≤ (304965861601/2500000000000 : ℝ)^6375
        have hw : |(-508638189/2500000000 : ℝ)|=(508638189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s3_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175346393/5000000000 : ℝ)*x 0 + (1134071659/2500000000 : ℝ)*x 1 + (834512203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175346393/5000000000 : ℝ)^8423 ≤ (16649973320143/50000000000000 : ℝ)^6375 := by
    have hnat : (2175346393 : ℕ)^8423*50000000000000^6375 ≤ 16649973320143^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175346393 5000000000 16649973320143 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134071659/2500000000 : ℝ)^8423 ≤ (35189560100857/100000000000000 : ℝ)^6375 := by
    have hnat : (1134071659 : ℕ)^8423*100000000000000^6375 ≤ 35189560100857^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134071659 2500000000 35189560100857 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834512203/2000000000 : ℝ)^8423 ≤ (3938811655527/12500000000000 : ℝ)^6375 := by
    have hnat : (834512203 : ℕ)^8423*12500000000000^6375 ≤ 3938811655527^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834512203 2000000000 3938811655527 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175346393/5000000000 : ℝ), (1134071659/2500000000 : ℝ), (834512203/2000000000 : ℝ)] ![(16649973320143/50000000000000 : ℝ), (35189560100857/100000000000000 : ℝ), (3938811655527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175346393/5000000000 : ℝ)|^8423 ≤ (16649973320143/50000000000000 : ℝ)^6375
        have hw : |(2175346393/5000000000 : ℝ)|=(2175346393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134071659/2500000000 : ℝ)|^8423 ≤ (35189560100857/100000000000000 : ℝ)^6375
        have hw : |(1134071659/2500000000 : ℝ)|=(1134071659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834512203/2000000000 : ℝ)|^8423 ≤ (3938811655527/12500000000000 : ℝ)^6375
        have hw : |(834512203/2000000000 : ℝ)|=(834512203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (68/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1839/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3251/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (189/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3251/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (189/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3251/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (189/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3251/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (189/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3251/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (189/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3251/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (189/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (189/2000 : ℝ) ^ (4211/1024 : ℝ) ≤ (611876006405033/10000000000000000000 : ℝ) := by
    have hpowers : (189/2000 : ℝ)^4211 ≤ (611876006405033/10000000000000000000 : ℝ)^1024 := by
      have hnat : (189 : ℕ)^4211*10000000000000000000^1024 ≤ 611876006405033^1024*2000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        189 2000 611876006405033 10000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (189/2000 : ℝ)) (X := (611876006405033/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3251/20000 : ℝ) ^ (4211/1024 : ℝ) ≤ (11385917420727267/20000000000000000000 : ℝ) := by
    have hpowers : (3251/20000 : ℝ)^4211 ≤ (11385917420727267/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3251 : ℕ)^4211*20000000000000000000^1024 ≤ 11385917420727267^1024*20000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3251 20000 11385917420727267 20000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3251/20000 : ℝ)) (X := (11385917420727267/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000611876006405033/5000000000000000000 : ℝ) ≤ (10000297569231807/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (5000611876006405033/5000000000000000000 : ℝ)^1024 ≤ (10000297569231807/10000000000000000 : ℝ)^4211 := by
      have hnat : (5000611876006405033 : ℕ)^1024*10000000000000000^4211 ≤ 10000297569231807^4211*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000611876006405033 5000000000000000000 10000297569231807 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000297569231807/10000000000000000 : ℝ)) (X := (5000611876006405033/5000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20012609669433537333/20000000000000000000 : ℝ) ≤ (10001532797669663/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (20012609669433537333/20000000000000000000 : ℝ)^1024 ≤ (10001532797669663/10000000000000000 : ℝ)^4211 := by
      have hnat : (20012609669433537333 : ℕ)^1024*10000000000000000^4211 ≤ 10001532797669663^4211*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20012609669433537333 20000000000000000000 10001532797669663 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001532797669663/10000000000000000 : ℝ)) (X := (20012609669433537333/20000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10011385917420727267/10000000000000000000 : ℝ) ≤ (10002768026107519/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (10011385917420727267/10000000000000000000 : ℝ)^1024 ≤ (10002768026107519/10000000000000000 : ℝ)^4211 := by
      have hnat : (10011385917420727267 : ℕ)^1024*10000000000000000^4211 ≤ 10002768026107519^4211*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011385917420727267 10000000000000000000 10002768026107519 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002768026107519/10000000000000000 : ℝ)) (X := (10011385917420727267/10000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(611876006405033/10000000000000000000 : ℝ) ≤ ((13605735828229393647/13610000000000000000 : ℝ)+2*(38600888683/21265625000000 : ℝ)*(189/2000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (13605735828229393647/13610000000000000000 : ℝ)+2*(38600888683/21265625000000 : ℝ)*(189/2000 : ℝ)=(10000297569231807/10000000000000000 : ℝ) by norm_num, show 1+2*(611876006405033/10000000000000000000 : ℝ)=(5000611876006405033/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11385917420727267/20000000000000000000 : ℝ)+(611876006405033/10000000000000000000 : ℝ) ≤ ((13605735828229393647/13610000000000000000 : ℝ)+(38600888683/21265625000000 : ℝ)*((3251/20000 : ℝ)+(189/2000 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (13605735828229393647/13610000000000000000 : ℝ)+(38600888683/21265625000000 : ℝ)*((3251/20000 : ℝ)+(189/2000 : ℝ))=(10001532797669663/10000000000000000 : ℝ) by norm_num, show 1+(11385917420727267/20000000000000000000 : ℝ)+(611876006405033/10000000000000000000 : ℝ)=(20012609669433537333/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11385917420727267/20000000000000000000 : ℝ) ≤ ((13605735828229393647/13610000000000000000 : ℝ)+2*(38600888683/21265625000000 : ℝ)*(3251/20000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (13605735828229393647/13610000000000000000 : ℝ)+2*(38600888683/21265625000000 : ℝ)*(3251/20000 : ℝ)=(10002768026107519/10000000000000000 : ℝ) by norm_num, show 1+2*(11385917420727267/20000000000000000000 : ℝ)=(10011385917420727267/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13605735828229393647/13610000000000000000 : ℝ)*(X 1 0+X 2 0)+(38600888683/21265625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (189/2000 : ℝ)) (hi := (3251/20000 : ℝ)) (c := (13605735828229393647/13610000000000000000 : ℝ)) (alpha := (38600888683/21265625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13605735828229393647/13610000000000000000 : ℝ)*(X 0 1+X 2 1)+(38600888683/21265625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (189/2000 : ℝ)) (hi := (3251/20000 : ℝ)) (c := (13605735828229393647/13610000000000000000 : ℝ)) (alpha := (38600888683/21265625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13605735828229393647/13610000000000000000 : ℝ)*(X 0 2+X 1 2)+(38600888683/21265625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (189/2000 : ℝ)) (hi := (3251/20000 : ℝ)) (c := (13605735828229393647/13610000000000000000 : ℝ)) (alpha := (38600888683/21265625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-265319151/1250000000 : ℝ)*X 0 0+(5420726393/10000000000 : ℝ)*X 0 1+(5239678429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070351513/2000000000 : ℝ)*X 1 0+(-442986683/2000000000 : ℝ)*X 1 1+(5239678601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351757449/10000000000 : ℝ)*X 2 0+(163739969/312500000 : ℝ)*X 2 1+(-2214933033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87013269/200000000 : ℝ)*X 0 0+(4171212083/10000000000 : ℝ)*X 0 1+(1134407161/2500000000 : ℝ)*X 0 2+(87013269/200000000 : ℝ)*X 1 0+(4171212083/10000000000 : ℝ)*X 1 1+(1134407161/2500000000 : ℝ)*X 1 2+(87013269/200000000 : ℝ)*X 2 0+(4171212083/10000000000 : ℝ)*X 2 1+(1134407161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2122567793/10000000000 : ℝ)*X 0 0+(2620170727/5000000000 : ℝ)*X 0 1+(1084011949/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652802783/5000000000 : ℝ)*X 1 0+(-1017275911/5000000000 : ℝ)*X 1 1+(338753729/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652802199/5000000000 : ℝ)*X 2 0+(2710030071/5000000000 : ℝ)*X 2 1+(-508638189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175346393/5000000000 : ℝ)*X 0 0+(1134071659/2500000000 : ℝ)*X 0 1+(834512203/2000000000 : ℝ)*X 0 2+(2175346393/5000000000 : ℝ)*X 1 0+(1134071659/2500000000 : ℝ)*X 1 1+(834512203/2000000000 : ℝ)*X 1 2+(2175346393/5000000000 : ℝ)*X 2 0+(1134071659/2500000000 : ℝ)*X 2 1+(834512203/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2458134767476272234479009331/340250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48371167/5000000000000 : ℝ)*(base19) + (72840723/12500000000000 : ℝ)*(base23) + (154023653/100000000000000 : ℝ)*(lower2) + (103334363/100000000000000 : ℝ)*(upper5) + (2063153596411403/50000000000000 : ℝ)*(major0) + (2063153596411403/50000000000000 : ℝ)*(major1) + (2063153596411403/50000000000000 : ℝ)*(major2) + (5523425364377661/100000000000000 : ℝ)*(sp0) + (5523455194380587/100000000000000 : ℝ)*(sp1) + (2761729112879747/50000000000000 : ℝ)*(sp2) + (34114313991103/1250000000000 : ℝ)*(sp3) + (33444107617/100000000000000 : ℝ)*(sp4) + (330835169/12500000000000 : ℝ)*(sp5) + (10217055547/100000000000000 : ℝ)*(sp7) + (682288834085947/25000000000000 : ℝ)*(f.failure) + (2761729404242639/50000000000000 : ℝ)*(f.sum) + (126748827007611/34025000000000000000000000000 : ℝ)*base65 + (6939688721394416741/680500000000000000000000000000000 : ℝ)*base67 + (6804158098466416741/680500000000000000000000000000000 : ℝ)*base69 + (10900285739651416741/680500000000000000000000000000000 : ℝ)*base71 + (150321697805361/34025000000000000000000000000 : ℝ)*base73 + (7560089971245916741/680500000000000000000000000000000 : ℝ)*base75 + (10130657307271916741/680500000000000000000000000000000 : ℝ)*base77 + (14313627509883916741/680500000000000000000000000000000 : ℝ)*base79 + (61545518765361/34025000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (25159161/2500000000000000000000 : ℝ)*base89 + (25159161/2500000000000000000000 : ℝ)*base91 + (25159161/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5533791399758561961307291443/680500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1584870291/100000000000000 : ℝ)*(base19) + (245661199/100000000000000 : ℝ)*(base23) + (24688809/100000000000000 : ℝ)*(upper3) + (111142631/100000000000000 : ℝ)*(lower4) + (127357161/50000000000000 : ℝ)*(upper5) + (4156788078845941/100000000000000 : ℝ)*(major0) + (4156788078845941/100000000000000 : ℝ)*(major1) + (4156788078845941/100000000000000 : ℝ)*(major2) + (422456441/50000000000000 : ℝ)*(sp0) + (37218012611/100000000000000 : ℝ)*(sp1) + (556425953094327/10000000000000 : ℝ)*(sp4) + (5564221572973251/100000000000000 : ℝ)*(sp5) + (5564260130194953/100000000000000 : ℝ)*(sp6) + (687328877692687/25000000000000 : ℝ)*(sp7) + (687328877692687/25000000000000 : ℝ)*(f.failure) + (695532546982019/12500000000000 : ℝ)*(f.sum) + (57736484174777/17012500000000000000000000000 : ℝ)*base66 + (16180912754366943173/1361000000000000000000000000000000 : ℝ)*base68 + (4568105146220943173/1361000000000000000000000000000000 : ℝ)*base70 + (12851577766641943173/1361000000000000000000000000000000 : ℝ)*base72 + (244625692097529/34025000000000000000000000000 : ℝ)*base74 + (29196211774487943173/1361000000000000000000000000000000 : ℝ)*base76 + (18805729580334943173/1361000000000000000000000000000000 : ℝ)*base78 + (6243508811686943173/1361000000000000000000000000000000 : ℝ)*base80 + (33645934019/2126562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (41573781/2500000000000000000000 : ℝ)*base89 + (41573781/2500000000000000000000 : ℝ)*base91 + (41573781/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1230_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1230_s4_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-212492203/1000000000 : ℝ)*x 0 + (168687029/312500000 : ℝ)*x 1 + (2630433939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212492203/1000000000 : ℝ)^8423 ≤ (6459793639369/50000000000000 : ℝ)^6375 := by
    have hnat : (212492203 : ℕ)^8423*50000000000000^6375 ≤ 6459793639369^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212492203 1000000000 6459793639369 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168687029/312500000 : ℝ)^8423 ≤ (11070055211343/25000000000000 : ℝ)^6375 := by
    have hnat : (168687029 : ℕ)^8423*25000000000000^6375 ≤ 11070055211343^6375*312500000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168687029 312500000 11070055211343 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630433939/5000000000 : ℝ)^8423 ≤ (5350023982179/12500000000000 : ℝ)^6375 := by
    have hnat : (2630433939 : ℕ)^8423*12500000000000^6375 ≤ 5350023982179^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630433939 5000000000 5350023982179 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212492203/1000000000 : ℝ), (168687029/312500000 : ℝ), (2630433939/5000000000 : ℝ)] ![(6459793639369/50000000000000 : ℝ), (11070055211343/25000000000000 : ℝ), (5350023982179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212492203/1000000000 : ℝ)|^8423 ≤ (6459793639369/50000000000000 : ℝ)^6375
        have hw : |(-212492203/1000000000 : ℝ)|=(212492203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168687029/312500000 : ℝ)|^8423 ≤ (11070055211343/25000000000000 : ℝ)^6375
        have hw : |(168687029/312500000 : ℝ)|=(168687029/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630433939/5000000000 : ℝ)|^8423 ≤ (5350023982179/12500000000000 : ℝ)^6375
        have hw : |(2630433939/5000000000 : ℝ)|=(2630433939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s4_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069206189/2000000000 : ℝ)*x 0 + (-1097272719/5000000000 : ℝ)*x 1 + (5260867827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069206189/2000000000 : ℝ)^8423 ≤ (43717995830003/100000000000000 : ℝ)^6375 := by
    have hnat : (1069206189 : ℕ)^8423*100000000000000^6375 ≤ 43717995830003^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069206189 2000000000 43717995830003 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097272719/5000000000 : ℝ)^8423 ≤ (3370453212331/25000000000000 : ℝ)^6375 := by
    have hnat : (1097272719 : ℕ)^8423*25000000000000^6375 ≤ 3370453212331^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097272719 5000000000 3370453212331 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260867827/10000000000 : ℝ)^8423 ≤ (5350023913653/12500000000000 : ℝ)^6375 := by
    have hnat : (5260867827 : ℕ)^8423*12500000000000^6375 ≤ 5350023913653^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260867827 10000000000 5350023913653 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069206189/2000000000 : ℝ), (-1097272719/5000000000 : ℝ), (5260867827/10000000000 : ℝ)] ![(43717995830003/100000000000000 : ℝ), (3370453212331/25000000000000 : ℝ), (5350023913653/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069206189/2000000000 : ℝ)|^8423 ≤ (43717995830003/100000000000000 : ℝ)^6375
        have hw : |(1069206189/2000000000 : ℝ)|=(1069206189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097272719/5000000000 : ℝ)|^8423 ≤ (3370453212331/25000000000000 : ℝ)^6375
        have hw : |(-1097272719/5000000000 : ℝ)|=(1097272719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260867827/10000000000 : ℝ)|^8423 ≤ (5350023913653/12500000000000 : ℝ)^6375
        have hw : |(5260867827/10000000000 : ℝ)|=(5260867827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s4_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346030787/10000000000 : ℝ)*x 0 + (5260867779/10000000000 : ℝ)*x 1 + (-137159107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346030787/10000000000 : ℝ)^8423 ≤ (874359882457/2000000000000 : ℝ)^6375 := by
    have hnat : (5346030787 : ℕ)^8423*2000000000000^6375 ≤ 874359882457^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346030787 10000000000 874359882457 2000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260867779/10000000000 : ℝ)^8423 ≤ (2675011924579/6250000000000 : ℝ)^6375 := by
    have hnat : (5260867779 : ℕ)^8423*6250000000000^6375 ≤ 2675011924579^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260867779 10000000000 2675011924579 6250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137159107/625000000 : ℝ)^8423 ≤ (3370453768339/25000000000000 : ℝ)^6375 := by
    have hnat : (137159107 : ℕ)^8423*25000000000000^6375 ≤ 3370453768339^6375*625000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137159107 625000000 3370453768339 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346030787/10000000000 : ℝ), (5260867779/10000000000 : ℝ), (-137159107/625000000 : ℝ)] ![(874359882457/2000000000000 : ℝ), (2675011924579/6250000000000 : ℝ), (3370453768339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346030787/10000000000 : ℝ)|^8423 ≤ (874359882457/2000000000000 : ℝ)^6375
        have hw : |(5346030787/10000000000 : ℝ)|=(5346030787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260867779/10000000000 : ℝ)|^8423 ≤ (2675011924579/6250000000000 : ℝ)^6375
        have hw : |(5260867779/10000000000 : ℝ)|=(5260867779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137159107/625000000 : ℝ)|^8423 ≤ (3370453768339/25000000000000 : ℝ)^6375
        have hw : |(-137159107/625000000 : ℝ)|=(137159107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s4_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352082823/10000000000 : ℝ)*x 0 + (4215485307/10000000000 : ℝ)*x 1 + (4492992547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352082823/10000000000 : ℝ)^8423 ≤ (33314004537961/100000000000000 : ℝ)^6375 := by
    have hnat : (4352082823 : ℕ)^8423*100000000000000^6375 ≤ 33314004537961^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352082823 10000000000 33314004537961 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4215485307/10000000000 : ℝ)^8423 ≤ (15969746794567/50000000000000 : ℝ)^6375 := by
    have hnat : (4215485307 : ℕ)^8423*50000000000000^6375 ≤ 15969746794567^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215485307 10000000000 15969746794567 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492992547/10000000000 : ℝ)^8423 ≤ (2171656365689/6250000000000 : ℝ)^6375 := by
    have hnat : (4492992547 : ℕ)^8423*6250000000000^6375 ≤ 2171656365689^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492992547 10000000000 2171656365689 6250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352082823/10000000000 : ℝ), (4215485307/10000000000 : ℝ), (4492992547/10000000000 : ℝ)] ![(33314004537961/100000000000000 : ℝ), (15969746794567/50000000000000 : ℝ), (2171656365689/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352082823/10000000000 : ℝ)|^8423 ≤ (33314004537961/100000000000000 : ℝ)^6375
        have hw : |(4352082823/10000000000 : ℝ)|=(4352082823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4215485307/10000000000 : ℝ)|^8423 ≤ (15969746794567/50000000000000 : ℝ)^6375
        have hw : |(4215485307/10000000000 : ℝ)|=(4215485307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492992547/10000000000 : ℝ)|^8423 ≤ (2171656365689/6250000000000 : ℝ)^6375
        have hw : |(4492992547/10000000000 : ℝ)|=(4492992547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s4_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124928247/10000000000 : ℝ)*x 0 + (5261248841/10000000000 : ℝ)*x 1 + (1349400621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124928247/10000000000 : ℝ)^8423 ≤ (12919637221589/100000000000000 : ℝ)^6375 := by
    have hnat : (2124928247 : ℕ)^8423*100000000000000^6375 ≤ 12919637221589^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124928247 10000000000 12919637221589 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261248841/10000000000 : ℝ)^8423 ≤ (10701071735281/25000000000000 : ℝ)^6375 := by
    have hnat : (5261248841 : ℕ)^8423*25000000000000^6375 ≤ 10701071735281^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261248841 10000000000 10701071735281 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349400621/2500000000 : ℝ)^8423 ≤ (44276075815817/100000000000000 : ℝ)^6375 := by
    have hnat : (1349400621 : ℕ)^8423*100000000000000^6375 ≤ 44276075815817^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349400621 2500000000 44276075815817 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124928247/10000000000 : ℝ), (5261248841/10000000000 : ℝ), (1349400621/2500000000 : ℝ)] ![(12919637221589/100000000000000 : ℝ), (10701071735281/25000000000000 : ℝ), (44276075815817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124928247/10000000000 : ℝ)|^8423 ≤ (12919637221589/100000000000000 : ℝ)^6375
        have hw : |(-2124928247/10000000000 : ℝ)|=(2124928247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261248841/10000000000 : ℝ)|^8423 ≤ (10701071735281/25000000000000 : ℝ)^6375
        have hw : |(5261248841/10000000000 : ℝ)|=(5261248841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349400621/2500000000 : ℝ)|^8423 ≤ (44276075815817/100000000000000 : ℝ)^6375
        have hw : |(1349400621/2500000000 : ℝ)|=(1349400621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s4_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311074849/10000000000 : ℝ)*x 0 + (-1028905699/5000000000 : ℝ)*x 1 + (5397602407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311074849/10000000000 : ℝ)^8423 ≤ (43340700650351/100000000000000 : ℝ)^6375 := by
    have hnat : (5311074849 : ℕ)^8423*100000000000000^6375 ≤ 43340700650351^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311074849 10000000000 43340700650351 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028905699/5000000000 : ℝ)^8423 ≤ (12383224360761/100000000000000 : ℝ)^6375 := by
    have hnat : (1028905699 : ℕ)^8423*100000000000000^6375 ≤ 12383224360761^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028905699 5000000000 12383224360761 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397602407/10000000000 : ℝ)^8423 ≤ (276725468633/625000000000 : ℝ)^6375 := by
    have hnat : (5397602407 : ℕ)^8423*625000000000^6375 ≤ 276725468633^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397602407 10000000000 276725468633 625000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311074849/10000000000 : ℝ), (-1028905699/5000000000 : ℝ), (5397602407/10000000000 : ℝ)] ![(43340700650351/100000000000000 : ℝ), (12383224360761/100000000000000 : ℝ), (276725468633/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311074849/10000000000 : ℝ)|^8423 ≤ (43340700650351/100000000000000 : ℝ)^6375
        have hw : |(5311074849/10000000000 : ℝ)|=(5311074849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028905699/5000000000 : ℝ)|^8423 ≤ (12383224360761/100000000000000 : ℝ)^6375
        have hw : |(-1028905699/5000000000 : ℝ)|=(1028905699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397602407/10000000000 : ℝ)|^8423 ≤ (276725468633/625000000000 : ℝ)^6375
        have hw : |(5397602407/10000000000 : ℝ)|=(5397602407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s4_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311074471/10000000000 : ℝ)*x 0 + (5397603059/10000000000 : ℝ)*x 1 + (-102890551/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311074471/10000000000 : ℝ)^8423 ≤ (10835174143687/25000000000000 : ℝ)^6375 := by
    have hnat : (5311074471 : ℕ)^8423*25000000000000^6375 ≤ 10835174143687^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311074471 10000000000 10835174143687 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397603059/10000000000 : ℝ)^8423 ≤ (44276082047749/100000000000000 : ℝ)^6375 := by
    have hnat : (5397603059 : ℕ)^8423*100000000000000^6375 ≤ 44276082047749^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397603059 10000000000 44276082047749 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102890551/500000000 : ℝ)^8423 ≤ (12383221355331/100000000000000 : ℝ)^6375 := by
    have hnat : (102890551 : ℕ)^8423*100000000000000^6375 ≤ 12383221355331^6375*500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102890551 500000000 12383221355331 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311074471/10000000000 : ℝ), (5397603059/10000000000 : ℝ), (-102890551/500000000 : ℝ)] ![(10835174143687/25000000000000 : ℝ), (44276082047749/100000000000000 : ℝ), (12383221355331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311074471/10000000000 : ℝ)|^8423 ≤ (10835174143687/25000000000000 : ℝ)^6375
        have hw : |(5311074471/10000000000 : ℝ)|=(5311074471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397603059/10000000000 : ℝ)|^8423 ≤ (44276082047749/100000000000000 : ℝ)^6375
        have hw : |(5397603059/10000000000 : ℝ)|=(5397603059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102890551/500000000 : ℝ)|^8423 ≤ (12383221355331/100000000000000 : ℝ)^6375
        have hw : |(-102890551/500000000 : ℝ)|=(102890551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s4_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435209583/1000000000 : ℝ)*x 0 + (561527753/1250000000 : ℝ)*x 1 + (4216258589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435209583/1000000000 : ℝ)^8423 ≤ (4164267011101/12500000000000 : ℝ)^6375 := by
    have hnat : (435209583 : ℕ)^8423*12500000000000^6375 ≤ 4164267011101^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435209583 1000000000 4164267011101 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561527753/1250000000 : ℝ)^8423 ≤ (2171164308409/6250000000000 : ℝ)^6375 := by
    have hnat : (561527753 : ℕ)^8423*6250000000000^6375 ≤ 2171164308409^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561527753 1250000000 2171164308409 6250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216258589/10000000000 : ℝ)^8423 ≤ (7986808739469/25000000000000 : ℝ)^6375 := by
    have hnat : (4216258589 : ℕ)^8423*25000000000000^6375 ≤ 7986808739469^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216258589 10000000000 7986808739469 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435209583/1000000000 : ℝ), (561527753/1250000000 : ℝ), (4216258589/10000000000 : ℝ)] ![(4164267011101/12500000000000 : ℝ), (2171164308409/6250000000000 : ℝ), (7986808739469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435209583/1000000000 : ℝ)|^8423 ≤ (4164267011101/12500000000000 : ℝ)^6375
        have hw : |(435209583/1000000000 : ℝ)|=(435209583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561527753/1250000000 : ℝ)|^8423 ≤ (2171164308409/6250000000000 : ℝ)^6375
        have hw : |(561527753/1250000000 : ℝ)|=(561527753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4216258589/10000000000 : ℝ)|^8423 ≤ (7986808739469/25000000000000 : ℝ)^6375
        have hw : |(4216258589/10000000000 : ℝ)|=(4216258589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    (2833/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (68/625 : ℝ) ^ (4211/1024 : ℝ) ≤ (10922561296073113/100000000000000000000 : ℝ) := by
    have hpowers : (68/625 : ℝ)^4211 ≤ (10922561296073113/100000000000000000000 : ℝ)^1024 := by
      have hnat : (68 : ℕ)^4211*100000000000000000000^1024 ≤ 10922561296073113^1024*625^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68 625 10922561296073113 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68/625 : ℝ)) (X := (10922561296073113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1839/12500 : ℝ) ^ (4211/1024 : ℝ) ≤ (4721962243016239/12500000000000000000 : ℝ) := by
    have hpowers : (1839/12500 : ℝ)^4211 ≤ (4721962243016239/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1839 : ℕ)^4211*12500000000000000000^1024 ≤ 4721962243016239^1024*12500^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 12500 4721962243016239 12500000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/12500 : ℝ)) (X := (4721962243016239/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010922561296073113/50000000000000000000 : ℝ) ≤ (2500132792428197/2500000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50010922561296073113/50000000000000000000 : ℝ)^1024 ≤ (2500132792428197/2500000000000000 : ℝ)^4211 := by
      have hnat : (50010922561296073113 : ℕ)^1024*2500000000000000^4211 ≤ 2500132792428197^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010922561296073113 50000000000000000000 2500132792428197 2500000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500132792428197/2500000000000000 : ℝ)) (X := (50010922561296073113/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001947930369608121/4000000000000000000 : ℝ) ≤ (10001183990276519/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (4001947930369608121/4000000000000000000 : ℝ)^1024 ≤ (10001183990276519/10000000000000000 : ℝ)^4211 := by
      have hnat : (4001947930369608121 : ℕ)^1024*10000000000000000^4211 ≤ 10001183990276519^4211*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001947930369608121 4000000000000000000 10001183990276519 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001183990276519/10000000000000000 : ℝ)) (X := (4001947930369608121/4000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254721962243016239/6250000000000000000 : ℝ) ≤ (40007347243361/40000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (6254721962243016239/6250000000000000000 : ℝ)^1024 ≤ (40007347243361/40000000000000 : ℝ)^4211 := by
      have hnat : (6254721962243016239 : ℕ)^1024*40000000000000^4211 ≤ 40007347243361^4211*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254721962243016239 6250000000000000000 40007347243361 40000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40007347243361/40000000000000 : ℝ)) (X := (6254721962243016239/6250000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10922561296073113/100000000000000000000 : ℝ) ≤ ((1197119689589769283/1197500000000000000 : ℝ)+2*(652820563731/383200000000000 : ℝ)*(68/625 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (1197119689589769283/1197500000000000000 : ℝ)+2*(652820563731/383200000000000 : ℝ)*(68/625 : ℝ)=(2500132792428197/2500000000000000 : ℝ) by norm_num, show 1+2*(10922561296073113/100000000000000000000 : ℝ)=(50010922561296073113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4721962243016239/12500000000000000000 : ℝ)+(10922561296073113/100000000000000000000 : ℝ) ≤ ((1197119689589769283/1197500000000000000 : ℝ)+(652820563731/383200000000000 : ℝ)*((1839/12500 : ℝ)+(68/625 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (1197119689589769283/1197500000000000000 : ℝ)+(652820563731/383200000000000 : ℝ)*((1839/12500 : ℝ)+(68/625 : ℝ))=(10001183990276519/10000000000000000 : ℝ) by norm_num, show 1+(4721962243016239/12500000000000000000 : ℝ)+(10922561296073113/100000000000000000000 : ℝ)=(4001947930369608121/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4721962243016239/12500000000000000000 : ℝ) ≤ ((1197119689589769283/1197500000000000000 : ℝ)+2*(652820563731/383200000000000 : ℝ)*(1839/12500 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (1197119689589769283/1197500000000000000 : ℝ)+2*(652820563731/383200000000000 : ℝ)*(1839/12500 : ℝ)=(40007347243361/40000000000000 : ℝ) by norm_num, show 1+2*(4721962243016239/12500000000000000000 : ℝ)=(6254721962243016239/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1197119689589769283/1197500000000000000 : ℝ)*(X 1 0+X 2 0)+(652820563731/383200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (1197119689589769283/1197500000000000000 : ℝ)) (alpha := (652820563731/383200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1197119689589769283/1197500000000000000 : ℝ)*(X 0 1+X 2 1)+(652820563731/383200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (1197119689589769283/1197500000000000000 : ℝ)) (alpha := (652820563731/383200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1197119689589769283/1197500000000000000 : ℝ)*(X 0 2+X 1 2)+(652820563731/383200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (1197119689589769283/1197500000000000000 : ℝ)) (alpha := (652820563731/383200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212492203/1000000000 : ℝ)*X 0 0+(168687029/312500000 : ℝ)*X 0 1+(2630433939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069206189/2000000000 : ℝ)*X 1 0+(-1097272719/5000000000 : ℝ)*X 1 1+(5260867827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346030787/10000000000 : ℝ)*X 2 0+(5260867779/10000000000 : ℝ)*X 2 1+(-137159107/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352082823/10000000000 : ℝ)*X 0 0+(4215485307/10000000000 : ℝ)*X 0 1+(4492992547/10000000000 : ℝ)*X 0 2+(4352082823/10000000000 : ℝ)*X 1 0+(4215485307/10000000000 : ℝ)*X 1 1+(4492992547/10000000000 : ℝ)*X 1 2+(4352082823/10000000000 : ℝ)*X 2 0+(4215485307/10000000000 : ℝ)*X 2 1+(4492992547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2124928247/10000000000 : ℝ)*X 0 0+(5261248841/10000000000 : ℝ)*X 0 1+(1349400621/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311074849/10000000000 : ℝ)*X 1 0+(-1028905699/5000000000 : ℝ)*X 1 1+(5397602407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311074471/10000000000 : ℝ)*X 2 0+(5397603059/10000000000 : ℝ)*X 2 1+(-102890551/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435209583/1000000000 : ℝ)*X 0 0+(561527753/1250000000 : ℝ)*X 0 1+(4216258589/10000000000 : ℝ)*X 0 2+(435209583/1000000000 : ℝ)*X 1 0+(561527753/1250000000 : ℝ)*X 1 1+(4216258589/10000000000 : ℝ)*X 1 2+(435209583/1000000000 : ℝ)*X 2 0+(561527753/1250000000 : ℝ)*X 2 1+(4216258589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23988846906547380880123749/5987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1577923533/100000000000000 : ℝ)*(base19) + (158635647/10000000000000 : ℝ)*(base23) + (36481981/25000000000000 : ℝ)*(upper2) + (28914659/10000000000000 : ℝ)*(upper3) + (6547097/25000000000000 : ℝ)*(upper4) + (544833429812149/10000000000000 : ℝ)*(major0) + (544833429812149/10000000000000 : ℝ)*(major1) + (544833429812149/10000000000000 : ℝ)*(major2) + (911636065857447/12500000000000 : ℝ)*(sp0) + (7293117771953781/100000000000000 : ℝ)*(sp1) + (1823279440880211/25000000000000 : ℝ)*(sp2) + (1801763823987443/50000000000000 : ℝ)*(sp3) + (15411508869/50000000000000 : ℝ)*(sp4) + (10732420587/50000000000000 : ℝ)*(sp7) + (180177455640803/5000000000000 : ℝ)*(f.failure) + (3646559674938657/50000000000000 : ℝ)*(f.sum) + (10264800521393/1916000000000000000000000000 : ℝ)*base66 + (7352043778133021/5987500000000000000000000000000 : ℝ)*base67 + (39250745307683021/5987500000000000000000000000000 : ℝ)*base69 + (6944820257620521/5987500000000000000000000000000 : ℝ)*base71 + (12651814763681/1916000000000000000000000000 : ℝ)*base74 + (13402988207229479/5987500000000000000000000000000 : ℝ)*base76 + (60141950950591979/5987500000000000000000000000000 : ℝ)*base78 + (95972592454258021/5987500000000000000000000000000 : ℝ)*base79 + (5589979267281/1916000000000000000000000000 : ℝ)*base82 + (3751089/500000000000000000000 : ℝ)*base89 + (3751089/500000000000000000000 : ℝ)*base91 + (3751089/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (438455617126093164409654629/59875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (887372923/100000000000000 : ℝ)*(base19) + (261661647/50000000000000 : ℝ)*(base23) + (2049411/50000000000000 : ℝ)*(lower2) + (351933589/100000000000000 : ℝ)*(upper3) + (18368077/12500000000000 : ℝ)*(upper5) + (5478768402779173/100000000000000 : ℝ)*(major0) + (5478768402779173/100000000000000 : ℝ)*(major1) + (5478768402779173/100000000000000 : ℝ)*(major2) + (251654551/1000000000000 : ℝ)*(sp2) + (755851967/20000000000000 : ℝ)*(sp3) + (7333858215594101/100000000000000 : ℝ)*(sp4) + (3666928664110589/50000000000000 : ℝ)*(sp5) + (1833458131703927/25000000000000 : ℝ)*(sp6) + (362367456660941/10000000000000 : ℝ)*(sp7) + (905919586467311/25000000000000 : ℝ)*(f.failure) + (7333858215594101/100000000000000 : ℝ)*(f.sum) + (5475601803183/19160000000000000000000000000 : ℝ)*base65 + (136564296050380083/59875000000000000000000000000000 : ℝ)*base68 + (1381308185381255083/59875000000000000000000000000000 : ℝ)*base70 + (351731327577244917/59875000000000000000000000000000 : ℝ)*base71 + (76460218039097/19160000000000000000000000000 : ℝ)*base74 + (3315739420531005083/59875000000000000000000000000000 : ℝ)*base76 + (53131569927005083/59875000000000000000000000000000 : ℝ)*base78 + (2081219676569005083/59875000000000000000000000000000 : ℝ)*base80 + (161820614870537/19160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (8119093/2500000000000000000000 : ℝ)*base89 + (8119093/2500000000000000000000 : ℝ)*base91 + (8119093/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1230_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1230_s5_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125390631/10000000000 : ℝ)*x 0 + (539269893/1000000000 : ℝ)*x 1 + (263292297/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125390631/10000000000 : ℝ)^8423 ≤ (12923351809467/100000000000000 : ℝ)^6375 := by
    have hnat : (2125390631 : ℕ)^8423*100000000000000^6375 ≤ 12923351809467^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125390631 10000000000 12923351809467 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539269893/1000000000 : ℝ)^8423 ≤ (1768917526323/4000000000000 : ℝ)^6375 := by
    have hnat : (539269893 : ℕ)^8423*4000000000000^6375 ≤ 1768917526323^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539269893 1000000000 1768917526323 4000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263292297/500000000 : ℝ)^8423 ≤ (8570742004731/20000000000000 : ℝ)^6375 := by
    have hnat : (263292297 : ℕ)^8423*20000000000000^6375 ≤ 8570742004731^6375*500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263292297 500000000 8570742004731 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125390631/10000000000 : ℝ), (539269893/1000000000 : ℝ), (263292297/500000000 : ℝ)] ![(12923351809467/100000000000000 : ℝ), (1768917526323/4000000000000 : ℝ), (8570742004731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125390631/10000000000 : ℝ)|^8423 ≤ (12923351809467/100000000000000 : ℝ)^6375
        have hw : |(-2125390631/10000000000 : ℝ)|=(2125390631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539269893/1000000000 : ℝ)|^8423 ≤ (1768917526323/4000000000000 : ℝ)^6375
        have hw : |(539269893/1000000000 : ℝ)|=(539269893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263292297/500000000 : ℝ)|^8423 ≤ (8570742004731/20000000000000 : ℝ)^6375
        have hw : |(263292297/500000000 : ℝ)|=(263292297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s5_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344694663/10000000000 : ℝ)*x 0 + (-437945789/2000000000 : ℝ)*x 1 + (82278843/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344694663/10000000000 : ℝ)^8423 ≤ (21851779097343/50000000000000 : ℝ)^6375 := by
    have hnat : (5344694663 : ℕ)^8423*50000000000000^6375 ≤ 21851779097343^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344694663 10000000000 21851779097343 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437945789/2000000000 : ℝ)^8423 ≤ (1680341454333/12500000000000 : ℝ)^6375 := by
    have hnat : (437945789 : ℕ)^8423*12500000000000^6375 ≤ 1680341454333^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437945789 2000000000 1680341454333 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82278843/156250000 : ℝ)^8423 ≤ (10713427538171/25000000000000 : ℝ)^6375 := by
    have hnat : (82278843 : ℕ)^8423*25000000000000^6375 ≤ 10713427538171^6375*156250000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82278843 156250000 10713427538171 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344694663/10000000000 : ℝ), (-437945789/2000000000 : ℝ), (82278843/156250000 : ℝ)] ![(21851779097343/50000000000000 : ℝ), (1680341454333/12500000000000 : ℝ), (10713427538171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344694663/10000000000 : ℝ)|^8423 ≤ (21851779097343/50000000000000 : ℝ)^6375
        have hw : |(5344694663/10000000000 : ℝ)|=(5344694663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437945789/2000000000 : ℝ)|^8423 ≤ (1680341454333/12500000000000 : ℝ)^6375
        have hw : |(-437945789/2000000000 : ℝ)|=(437945789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82278843/156250000 : ℝ)|^8423 ≤ (10713427538171/25000000000000 : ℝ)^6375
        have hw : |(82278843/156250000 : ℝ)|=(82278843/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s5_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344694819/10000000000 : ℝ)*x 0 + (1316461511/2500000000 : ℝ)*x 1 + (-2189728617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344694819/10000000000 : ℝ)^8423 ≤ (21851779940047/50000000000000 : ℝ)^6375 := by
    have hnat : (5344694819 : ℕ)^8423*50000000000000^6375 ≤ 21851779940047^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344694819 10000000000 21851779940047 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316461511/2500000000 : ℝ)^8423 ≤ (42853711141909/100000000000000 : ℝ)^6375 := by
    have hnat : (1316461511 : ℕ)^8423*100000000000000^6375 ≤ 42853711141909^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316461511 2500000000 42853711141909 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189728617/10000000000 : ℝ)^8423 ≤ (13442728974199/100000000000000 : ℝ)^6375 := by
    have hnat : (2189728617 : ℕ)^8423*100000000000000^6375 ≤ 13442728974199^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189728617 10000000000 13442728974199 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344694819/10000000000 : ℝ), (1316461511/2500000000 : ℝ), (-2189728617/10000000000 : ℝ)] ![(21851779940047/50000000000000 : ℝ), (42853711141909/100000000000000 : ℝ), (13442728974199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344694819/10000000000 : ℝ)|^8423 ≤ (21851779940047/50000000000000 : ℝ)^6375
        have hw : |(5344694819/10000000000 : ℝ)|=(5344694819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316461511/2500000000 : ℝ)|^8423 ≤ (42853711141909/100000000000000 : ℝ)^6375
        have hw : |(1316461511/2500000000 : ℝ)|=(1316461511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2189728617/10000000000 : ℝ)|^8423 ≤ (13442728974199/100000000000000 : ℝ)^6375
        have hw : |(-2189728617/10000000000 : ℝ)|=(2189728617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s5_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352357763/10000000000 : ℝ)*x 0 + (422583759/1000000000 : ℝ)*x 1 + (448257011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352357763/10000000000 : ℝ)^8423 ≤ (16658392633383/50000000000000 : ℝ)^6375 := by
    have hnat : (4352357763 : ℕ)^8423*50000000000000^6375 ≤ 16658392633383^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352357763 10000000000 16658392633383 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422583759/1000000000 : ℝ)^8423 ≤ (32043168668981/100000000000000 : ℝ)^6375 := by
    have hnat : (422583759 : ℕ)^8423*100000000000000^6375 ≤ 32043168668981^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422583759 1000000000 32043168668981 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448257011/1000000000 : ℝ)^8423 ≤ (3464004604739/10000000000000 : ℝ)^6375 := by
    have hnat : (448257011 : ℕ)^8423*10000000000000^6375 ≤ 3464004604739^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448257011 1000000000 3464004604739 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352357763/10000000000 : ℝ), (422583759/1000000000 : ℝ), (448257011/1000000000 : ℝ)] ![(16658392633383/50000000000000 : ℝ), (32043168668981/100000000000000 : ℝ), (3464004604739/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352357763/10000000000 : ℝ)|^8423 ≤ (16658392633383/50000000000000 : ℝ)^6375
        have hw : |(4352357763/10000000000 : ℝ)|=(4352357763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422583759/1000000000 : ℝ)|^8423 ≤ (32043168668981/100000000000000 : ℝ)^6375
        have hw : |(422583759/1000000000 : ℝ)|=(422583759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448257011/1000000000 : ℝ)|^8423 ≤ (3464004604739/10000000000000 : ℝ)^6375
        have hw : |(448257011/1000000000 : ℝ)|=(448257011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s5_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125395539/10000000000 : ℝ)*x 0 + (1316543069/2500000000 : ℝ)*x 1 + (2696185717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125395539/10000000000 : ℝ)^8423 ≤ (6461695619777/50000000000000 : ℝ)^6375 := by
    have hnat : (2125395539 : ℕ)^8423*50000000000000^6375 ≤ 6461695619777^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125395539 10000000000 6461695619777 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316543069/2500000000 : ℝ)^8423 ≤ (42857218965723/100000000000000 : ℝ)^6375 := by
    have hnat : (1316543069 : ℕ)^8423*100000000000000^6375 ≤ 42857218965723^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316543069 2500000000 42857218965723 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696185717/5000000000 : ℝ)^8423 ≤ (22109694890381/50000000000000 : ℝ)^6375 := by
    have hnat : (2696185717 : ℕ)^8423*50000000000000^6375 ≤ 22109694890381^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696185717 5000000000 22109694890381 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125395539/10000000000 : ℝ), (1316543069/2500000000 : ℝ), (2696185717/5000000000 : ℝ)] ![(6461695619777/50000000000000 : ℝ), (42857218965723/100000000000000 : ℝ), (22109694890381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125395539/10000000000 : ℝ)|^8423 ≤ (6461695619777/50000000000000 : ℝ)^6375
        have hw : |(-2125395539/10000000000 : ℝ)|=(2125395539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316543069/2500000000 : ℝ)|^8423 ≤ (42857218965723/100000000000000 : ℝ)^6375
        have hw : |(1316543069/2500000000 : ℝ)|=(1316543069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696185717/5000000000 : ℝ)|^8423 ≤ (22109694890381/50000000000000 : ℝ)^6375
        have hw : |(2696185717/5000000000 : ℝ)|=(2696185717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s5_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312354299/10000000000 : ℝ)*x 0 + (-1031601729/5000000000 : ℝ)*x 1 + (5392371433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312354299/10000000000 : ℝ)^8423 ≤ (43354496239123/100000000000000 : ℝ)^6375 := by
    have hnat : (5312354299 : ℕ)^8423*100000000000000^6375 ≤ 43354496239123^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312354299 10000000000 43354496239123 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031601729/5000000000 : ℝ)^8423 ≤ (6213056987723/50000000000000 : ℝ)^6375 := by
    have hnat : (1031601729 : ℕ)^8423*50000000000000^6375 ≤ 6213056987723^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031601729 5000000000 6213056987723 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392371433/10000000000 : ℝ)^8423 ≤ (44219389769927/100000000000000 : ℝ)^6375 := by
    have hnat : (5392371433 : ℕ)^8423*100000000000000^6375 ≤ 44219389769927^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392371433 10000000000 44219389769927 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312354299/10000000000 : ℝ), (-1031601729/5000000000 : ℝ), (5392371433/10000000000 : ℝ)] ![(43354496239123/100000000000000 : ℝ), (6213056987723/50000000000000 : ℝ), (44219389769927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312354299/10000000000 : ℝ)|^8423 ≤ (43354496239123/100000000000000 : ℝ)^6375
        have hw : |(5312354299/10000000000 : ℝ)|=(5312354299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031601729/5000000000 : ℝ)|^8423 ≤ (6213056987723/50000000000000 : ℝ)^6375
        have hw : |(-1031601729/5000000000 : ℝ)|=(1031601729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392371433/10000000000 : ℝ)|^8423 ≤ (44219389769927/100000000000000 : ℝ)^6375
        have hw : |(5392371433/10000000000 : ℝ)|=(5392371433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s5_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312354299/10000000000 : ℝ)*x 0 + (5392371433/10000000000 : ℝ)*x 1 + (-1031601729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312354299/10000000000 : ℝ)^8423 ≤ (43354496239123/100000000000000 : ℝ)^6375 := by
    have hnat : (5312354299 : ℕ)^8423*100000000000000^6375 ≤ 43354496239123^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312354299 10000000000 43354496239123 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392371433/10000000000 : ℝ)^8423 ≤ (44219389769927/100000000000000 : ℝ)^6375 := by
    have hnat : (5392371433 : ℕ)^8423*100000000000000^6375 ≤ 44219389769927^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392371433 10000000000 44219389769927 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031601729/5000000000 : ℝ)^8423 ≤ (6213056987723/50000000000000 : ℝ)^6375 := by
    have hnat : (1031601729 : ℕ)^8423*50000000000000^6375 ≤ 6213056987723^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031601729 5000000000 6213056987723 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312354299/10000000000 : ℝ), (5392371433/10000000000 : ℝ), (-1031601729/5000000000 : ℝ)] ![(43354496239123/100000000000000 : ℝ), (44219389769927/100000000000000 : ℝ), (6213056987723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312354299/10000000000 : ℝ)|^8423 ≤ (43354496239123/100000000000000 : ℝ)^6375
        have hw : |(5312354299/10000000000 : ℝ)|=(5312354299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392371433/10000000000 : ℝ)|^8423 ≤ (44219389769927/100000000000000 : ℝ)^6375
        have hw : |(5392371433/10000000000 : ℝ)|=(5392371433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031601729/5000000000 : ℝ)|^8423 ≤ (6213056987723/50000000000000 : ℝ)^6375
        have hw : |(-1031601729/5000000000 : ℝ)|=(1031601729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s5_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352368211/10000000000 : ℝ)*x 0 + (896382059/2000000000 : ℝ)*x 1 + (4226499447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352368211/10000000000 : ℝ)^8423 ≤ (16658445469203/50000000000000 : ℝ)^6375 := by
    have hnat : (4352368211 : ℕ)^8423*50000000000000^6375 ≤ 16658445469203^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352368211 10000000000 16658445469203 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896382059/2000000000 : ℝ)^8423 ≤ (17316654652837/50000000000000 : ℝ)^6375 := by
    have hnat : (896382059 : ℕ)^8423*50000000000000^6375 ≤ 17316654652837^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896382059 2000000000 17316654652837 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226499447/10000000000 : ℝ)^8423 ≤ (2003112484397/6250000000000 : ℝ)^6375 := by
    have hnat : (4226499447 : ℕ)^8423*6250000000000^6375 ≤ 2003112484397^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226499447 10000000000 2003112484397 6250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352368211/10000000000 : ℝ), (896382059/2000000000 : ℝ), (4226499447/10000000000 : ℝ)] ![(16658445469203/50000000000000 : ℝ), (17316654652837/50000000000000 : ℝ), (2003112484397/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352368211/10000000000 : ℝ)|^8423 ≤ (16658445469203/50000000000000 : ℝ)^6375
        have hw : |(4352368211/10000000000 : ℝ)|=(4352368211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896382059/2000000000 : ℝ)|^8423 ≤ (17316654652837/50000000000000 : ℝ)^6375
        have hw : |(896382059/2000000000 : ℝ)|=(896382059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226499447/10000000000 : ℝ)|^8423 ≤ (2003112484397/6250000000000 : ℝ)^6375
        have hw : |(4226499447/10000000000 : ℝ)|=(4226499447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5719/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (113/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2833/25000 : ℝ) ^ (4211/1024 : ℝ) ≤ (12912800989968771/100000000000000000000 : ℝ) := by
    have hpowers : (2833/25000 : ℝ)^4211 ≤ (12912800989968771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2833 : ℕ)^4211*100000000000000000000^1024 ≤ 12912800989968771^1024*25000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2833 25000 12912800989968771 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2833/25000 : ℝ)) (X := (12912800989968771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (4211/1024 : ℝ) ≤ (1031153785799551/3125000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^4211 ≤ (1031153785799551/3125000000000000000 : ℝ)^1024 := by
      have hnat : (3559 : ℕ)^4211*3125000000000000000^1024 ≤ 1031153785799551^1024*25000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 1031153785799551 3125000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (1031153785799551/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012912800989968771/50000000000000000000 : ℝ) ≤ (5000313973312407/5000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50012912800989968771/50000000000000000000 : ℝ)^1024 ≤ (5000313973312407/5000000000000000 : ℝ)^4211 := by
      have hnat : (50012912800989968771 : ℕ)^1024*5000000000000000^4211 ≤ 5000313973312407^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012912800989968771 50000000000000000000 5000313973312407 5000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000313973312407/5000000000000000 : ℝ)) (X := (50012912800989968771/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045909722135554403/100000000000000000000 : ℝ) ≤ (10001116204949109/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (100045909722135554403/100000000000000000000 : ℝ)^1024 ≤ (10001116204949109/10000000000000000 : ℝ)^4211 := by
      have hnat : (100045909722135554403 : ℕ)^1024*10000000000000000^4211 ≤ 10001116204949109^4211*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045909722135554403 100000000000000000000 10001116204949109 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001116204949109/10000000000000000 : ℝ)) (X := (100045909722135554403/100000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563531153785799551/1562500000000000000 : ℝ) ≤ (2500401115818351/2500000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (1563531153785799551/1562500000000000000 : ℝ)^1024 ≤ (2500401115818351/2500000000000000 : ℝ)^4211 := by
      have hnat : (1563531153785799551 : ℕ)^1024*2500000000000000^4211 ≤ 2500401115818351^4211*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563531153785799551 1562500000000000000 2500401115818351 2500000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500401115818351/2500000000000000 : ℝ)) (X := (1563531153785799551/1562500000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12912800989968771/100000000000000000000 : ℝ) ≤ ((1209614902930693249/1210000000000000000 : ℝ)+2*(32550554953/19360000000000 : ℝ)*(2833/25000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (1209614902930693249/1210000000000000000 : ℝ)+2*(32550554953/19360000000000 : ℝ)*(2833/25000 : ℝ)=(5000313973312407/5000000000000000 : ℝ) by norm_num, show 1+2*(12912800989968771/100000000000000000000 : ℝ)=(50012912800989968771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1031153785799551/3125000000000000000 : ℝ)+(12912800989968771/100000000000000000000 : ℝ) ≤ ((1209614902930693249/1210000000000000000 : ℝ)+(32550554953/19360000000000 : ℝ)*((3559/25000 : ℝ)+(2833/25000 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (1209614902930693249/1210000000000000000 : ℝ)+(32550554953/19360000000000 : ℝ)*((3559/25000 : ℝ)+(2833/25000 : ℝ))=(10001116204949109/10000000000000000 : ℝ) by norm_num, show 1+(1031153785799551/3125000000000000000 : ℝ)+(12912800989968771/100000000000000000000 : ℝ)=(100045909722135554403/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1031153785799551/3125000000000000000 : ℝ) ≤ ((1209614902930693249/1210000000000000000 : ℝ)+2*(32550554953/19360000000000 : ℝ)*(3559/25000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (1209614902930693249/1210000000000000000 : ℝ)+2*(32550554953/19360000000000 : ℝ)*(3559/25000 : ℝ)=(2500401115818351/2500000000000000 : ℝ) by norm_num, show 1+2*(1031153785799551/3125000000000000000 : ℝ)=(1563531153785799551/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1209614902930693249/1210000000000000000 : ℝ)*(X 1 0+X 2 0)+(32550554953/19360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1209614902930693249/1210000000000000000 : ℝ)) (alpha := (32550554953/19360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1209614902930693249/1210000000000000000 : ℝ)*(X 0 1+X 2 1)+(32550554953/19360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1209614902930693249/1210000000000000000 : ℝ)) (alpha := (32550554953/19360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1209614902930693249/1210000000000000000 : ℝ)*(X 0 2+X 1 2)+(32550554953/19360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1209614902930693249/1210000000000000000 : ℝ)) (alpha := (32550554953/19360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2125390631/10000000000 : ℝ)*X 0 0+(539269893/1000000000 : ℝ)*X 0 1+(263292297/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344694663/10000000000 : ℝ)*X 1 0+(-437945789/2000000000 : ℝ)*X 1 1+(82278843/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344694819/10000000000 : ℝ)*X 2 0+(1316461511/2500000000 : ℝ)*X 2 1+(-2189728617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352357763/10000000000 : ℝ)*X 0 0+(422583759/1000000000 : ℝ)*X 0 1+(448257011/1000000000 : ℝ)*X 0 2+(4352357763/10000000000 : ℝ)*X 1 0+(422583759/1000000000 : ℝ)*X 1 1+(448257011/1000000000 : ℝ)*X 1 2+(4352357763/10000000000 : ℝ)*X 2 0+(422583759/1000000000 : ℝ)*X 2 1+(448257011/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125395539/10000000000 : ℝ)*X 0 0+(1316543069/2500000000 : ℝ)*X 0 1+(2696185717/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312354299/10000000000 : ℝ)*X 1 0+(-1031601729/5000000000 : ℝ)*X 1 1+(5392371433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312354299/10000000000 : ℝ)*X 2 0+(5392371433/10000000000 : ℝ)*X 2 1+(-1031601729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352368211/10000000000 : ℝ)*X 0 0+(896382059/2000000000 : ℝ)*X 0 1+(4226499447/10000000000 : ℝ)*X 0 2+(4352368211/10000000000 : ℝ)*X 1 0+(896382059/2000000000 : ℝ)*X 1 1+(4226499447/10000000000 : ℝ)*X 1 2+(4352368211/10000000000 : ℝ)*X 2 0+(896382059/2000000000 : ℝ)*X 2 1+(4226499447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38214114050296378371777201/6050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269823453/20000000000000 : ℝ)*(base19) + (267910873/20000000000000 : ℝ)*(base23) + (78053369/50000000000000 : ℝ)*(upper4) + (148635387/100000000000000 : ℝ)*(upper5) + (588918879855683/10000000000000 : ℝ)*(major0) + (588918879855683/10000000000000 : ℝ)*(major1) + (588918879855683/10000000000000 : ℝ)*(major2) + (3941592766618727/50000000000000 : ℝ)*(sp0) + (1576647082234019/20000000000000 : ℝ)*(sp1) + (7883244083917107/100000000000000 : ℝ)*(sp2) + (389511824249541/10000000000000 : ℝ)*(sp3) + (59890234017/100000000000000 : ℝ)*(sp4) + (541449007/6250000000000 : ℝ)*(sp5) + (2744120137/20000000000000 : ℝ)*(sp7) + (1947565981548047/50000000000000 : ℝ)*(f.failure) + (492702838966967/6250000000000 : ℝ)*(f.sum) + (863923055143/484000000000000000000000000 : ℝ)*base65 + (177793590476628433/12100000000000000000000000000000 : ℝ)*base68 + (86692358283228433/12100000000000000000000000000000 : ℝ)*base70 + (119838071916271567/12100000000000000000000000000000 : ℝ)*base71 + (1053010334041/484000000000000000000000000 : ℝ)*base74 + (130975584939028433/12100000000000000000000000000000 : ℝ)*base76 + (56131957180271567/12100000000000000000000000000000 : ℝ)*base77 + (187723307808228433/12100000000000000000000000000000 : ℝ)*base80 + (2760422154089/484000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (18378539/5000000000000000000000 : ℝ)*base90 + (18378539/5000000000000000000000 : ℝ)*base92 + (18378539/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132840776313354264972691959/30250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158063277/20000000000000 : ℝ)*(base19) + (34318467/4000000000000 : ℝ)*(base23) + (4399703/5000000000000 : ℝ)*(upper3) + (7701539/25000000000000 : ℝ)*(lower4) + (89745579/100000000000000 : ℝ)*(upper5) + (5919621359045847/100000000000000 : ℝ)*(major0) + (5919621359045847/100000000000000 : ℝ)*(major1) + (5919621359045847/100000000000000 : ℝ)*(major2) + (10881680793/50000000000000 : ℝ)*(sp1) + (5837330561/25000000000000 : ℝ)*(sp2) + (198099559922011/2500000000000 : ℝ)*(sp4) + (7923959843202469/100000000000000 : ℝ)*(sp5) + (3961979094798261/50000000000000 : ℝ)*(sp6) + (1957630087415113/50000000000000 : ℝ)*(sp7) + (1957630087415113/50000000000000 : ℝ)*(f.failure) + (198099559922011/2500000000000 : ℝ)*(f.sum) + (1580864962977/968000000000000000000000000 : ℝ)*base66 + (329152816788675597/121000000000000000000000000000000 : ℝ)*base68 + (402572939300675597/121000000000000000000000000000000 : ℝ)*base70 + (296732963113675597/121000000000000000000000000000000 : ℝ)*base72 + (917149540673/968000000000000000000000000 : ℝ)*base74 + (2349969305030324403/121000000000000000000000000000000 : ℝ)*base75 + (978861045078675597/121000000000000000000000000000000 : ℝ)*base78 + (1498360972750675597/121000000000000000000000000000000 : ℝ)*base80 + (2722395295073/968000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (44517619/5000000000000000000000 : ℝ)*base89 + (44517619/5000000000000000000000 : ℝ)*base91 + (44517619/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1230_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1230_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1230_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1230_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1230_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
