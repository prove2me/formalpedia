-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1105_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:02:35.090434+00:00
-- url     : https://prove2.me/submissions/e5ff1545-d572-40ff-b3d0-aa659c673b95

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
theorem support_rectangle_w1105_s3_0 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-136279839/625000000 : ℝ)*x 0 + (13582781/25000000 : ℝ)*x 1 + (5228472837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136279839/625000000 : ℝ)^4149 ≤ (529502691851/4000000000000 : ℝ)^3125 := by
    have hnat : (136279839 : ℕ)^4149*4000000000000^3125 ≤ 529502691851^3125*625000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136279839 625000000 529502691851 4000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13582781/25000000 : ℝ)^4149 ≤ (44486623507897/100000000000000 : ℝ)^3125 := by
    have hnat : (13582781 : ℕ)^4149*100000000000000^3125 ≤ 44486623507897^3125*25000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13582781 25000000 44486623507897 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228472837/10000000000 : ℝ)^4149 ≤ (21137904589989/50000000000000 : ℝ)^3125 := by
    have hnat : (5228472837 : ℕ)^4149*50000000000000^3125 ≤ 21137904589989^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228472837 10000000000 21137904589989 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136279839/625000000 : ℝ), (13582781/25000000 : ℝ), (5228472837/10000000000 : ℝ)] ![(529502691851/4000000000000 : ℝ), (44486623507897/100000000000000 : ℝ), (21137904589989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136279839/625000000 : ℝ)|^4149 ≤ (529502691851/4000000000000 : ℝ)^3125
        have hw : |(-136279839/625000000 : ℝ)|=(136279839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13582781/25000000 : ℝ)|^4149 ≤ (44486623507897/100000000000000 : ℝ)^3125
        have hw : |(13582781/25000000 : ℝ)|=(13582781/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228472837/10000000000 : ℝ)|^4149 ≤ (21137904589989/50000000000000 : ℝ)^3125
        have hw : |(5228472837/10000000000 : ℝ)|=(5228472837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s3_1 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070939797/2000000000 : ℝ)*x 0 + (-1142584907/5000000000 : ℝ)*x 1 + (1307118239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070939797/2000000000 : ℝ)^4149 ≤ (10909051090877/25000000000000 : ℝ)^3125 := by
    have hnat : (1070939797 : ℕ)^4149*25000000000000^3125 ≤ 10909051090877^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070939797 2000000000 10909051090877 25000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142584907/5000000000 : ℝ)^4149 ≤ (2817597033237/20000000000000 : ℝ)^3125 := by
    have hnat : (1142584907 : ℕ)^4149*20000000000000^3125 ≤ 2817597033237^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142584907 5000000000 2817597033237 20000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307118239/2500000000 : ℝ)^4149 ≤ (10568952614367/25000000000000 : ℝ)^3125 := by
    have hnat : (1307118239 : ℕ)^4149*25000000000000^3125 ≤ 10568952614367^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307118239 2500000000 10568952614367 25000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070939797/2000000000 : ℝ), (-1142584907/5000000000 : ℝ), (1307118239/2500000000 : ℝ)] ![(10909051090877/25000000000000 : ℝ), (2817597033237/20000000000000 : ℝ), (10568952614367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070939797/2000000000 : ℝ)|^4149 ≤ (10909051090877/25000000000000 : ℝ)^3125
        have hw : |(1070939797/2000000000 : ℝ)|=(1070939797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142584907/5000000000 : ℝ)|^4149 ≤ (2817597033237/20000000000000 : ℝ)^3125
        have hw : |(-1142584907/5000000000 : ℝ)|=(1142584907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307118239/2500000000 : ℝ)|^4149 ≤ (10568952614367/25000000000000 : ℝ)^3125
        have hw : |(1307118239/2500000000 : ℝ)|=(1307118239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s3_2 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338674781/2500000000 : ℝ)*x 0 + (5228473053/10000000000 : ℝ)*x 1 + (-2285169503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338674781/2500000000 : ℝ)^4149 ≤ (10909051466853/25000000000000 : ℝ)^3125 := by
    have hnat : (1338674781 : ℕ)^4149*25000000000000^3125 ≤ 10909051466853^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338674781 2500000000 10909051466853 25000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228473053/10000000000 : ℝ)^4149 ≤ (42275811498783/100000000000000 : ℝ)^3125 := by
    have hnat : (5228473053 : ℕ)^4149*100000000000000^3125 ≤ 42275811498783^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228473053 10000000000 42275811498783 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285169503/10000000000 : ℝ)^4149 ≤ (704399131031/5000000000000 : ℝ)^3125 := by
    have hnat : (2285169503 : ℕ)^4149*5000000000000^3125 ≤ 704399131031^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285169503 10000000000 704399131031 5000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338674781/2500000000 : ℝ), (5228473053/10000000000 : ℝ), (-2285169503/10000000000 : ℝ)] ![(10909051466853/25000000000000 : ℝ), (42275811498783/100000000000000 : ℝ), (704399131031/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338674781/2500000000 : ℝ)|^4149 ≤ (10909051466853/25000000000000 : ℝ)^3125
        have hw : |(1338674781/2500000000 : ℝ)|=(1338674781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228473053/10000000000 : ℝ)|^4149 ≤ (42275811498783/100000000000000 : ℝ)^3125
        have hw : |(5228473053/10000000000 : ℝ)|=(5228473053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285169503/10000000000 : ℝ)|^4149 ≤ (704399131031/5000000000000 : ℝ)^3125
        have hw : |(-2285169503/10000000000 : ℝ)|=(2285169503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s3_3 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183702173/5000000000 : ℝ)*x 0 + (521250559/1250000000 : ℝ)*x 1 + (4574176061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183702173/5000000000 : ℝ)^4149 ≤ (33291380635867/100000000000000 : ℝ)^3125 := by
    have hnat : (2183702173 : ℕ)^4149*100000000000000^3125 ≤ 33291380635867^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183702173 5000000000 33291380635867 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521250559/1250000000 : ℝ)^4149 ≤ (15654271443291/50000000000000 : ℝ)^3125 := by
    have hnat : (521250559 : ℕ)^4149*50000000000000^3125 ≤ 15654271443291^3125*1250000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521250559 1250000000 15654271443291 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4574176061/10000000000 : ℝ)^4149 ≤ (35400076464627/100000000000000 : ℝ)^3125 := by
    have hnat : (4574176061 : ℕ)^4149*100000000000000^3125 ≤ 35400076464627^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574176061 10000000000 35400076464627 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183702173/5000000000 : ℝ), (521250559/1250000000 : ℝ), (4574176061/10000000000 : ℝ)] ![(33291380635867/100000000000000 : ℝ), (15654271443291/50000000000000 : ℝ), (35400076464627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183702173/5000000000 : ℝ)|^4149 ≤ (33291380635867/100000000000000 : ℝ)^3125
        have hw : |(2183702173/5000000000 : ℝ)|=(2183702173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521250559/1250000000 : ℝ)|^4149 ≤ (15654271443291/50000000000000 : ℝ)^3125
        have hw : |(521250559/1250000000 : ℝ)|=(521250559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4574176061/10000000000 : ℝ)|^4149 ≤ (35400076464627/100000000000000 : ℝ)^3125
        have hw : |(4574176061/10000000000 : ℝ)|=(4574176061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s3_4 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180497359/10000000000 : ℝ)*x 0 + (2614644107/5000000000 : ℝ)*x 1 + (1358073099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180497359/10000000000 : ℝ)^4149 ≤ (264754559563/2000000000000 : ℝ)^3125 := by
    have hnat : (2180497359 : ℕ)^4149*2000000000000^3125 ≤ 264754559563^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180497359 10000000000 264754559563 2000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614644107/5000000000 : ℝ)^4149 ≤ (42284562645769/100000000000000 : ℝ)^3125 := by
    have hnat : (2614644107 : ℕ)^4149*100000000000000^3125 ≤ 42284562645769^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614644107 5000000000 42284562645769 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358073099/2500000000 : ℝ)^4149 ≤ (8895541873791/20000000000000 : ℝ)^3125 := by
    have hnat : (1358073099 : ℕ)^4149*20000000000000^3125 ≤ 8895541873791^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358073099 2500000000 8895541873791 20000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180497359/10000000000 : ℝ), (2614644107/5000000000 : ℝ), (1358073099/2500000000 : ℝ)] ![(264754559563/2000000000000 : ℝ), (42284562645769/100000000000000 : ℝ), (8895541873791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180497359/10000000000 : ℝ)|^4149 ≤ (264754559563/2000000000000 : ℝ)^3125
        have hw : |(-2180497359/10000000000 : ℝ)|=(2180497359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614644107/5000000000 : ℝ)|^4149 ≤ (42284562645769/100000000000000 : ℝ)^3125
        have hw : |(2614644107/5000000000 : ℝ)|=(2614644107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358073099/2500000000 : ℝ)|^4149 ≤ (8895541873791/20000000000000 : ℝ)^3125
        have hw : |(1358073099/2500000000 : ℝ)|=(1358073099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s3_5 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212119869/400000000 : ℝ)*x 0 + (-1040675097/5000000000 : ℝ)*x 1 + (1086458521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212119869/400000000 : ℝ)^4149 ≤ (21538850513631/50000000000000 : ℝ)^3125 := by
    have hnat : (212119869 : ℕ)^4149*50000000000000^3125 ≤ 21538850513631^3125*400000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212119869 400000000 21538850513631 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040675097/5000000000 : ℝ)^4149 ≤ (12444587313731/100000000000000 : ℝ)^3125 := by
    have hnat : (1040675097 : ℕ)^4149*100000000000000^3125 ≤ 12444587313731^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040675097 5000000000 12444587313731 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086458521/2000000000 : ℝ)^4149 ≤ (22238855820453/50000000000000 : ℝ)^3125 := by
    have hnat : (1086458521 : ℕ)^4149*50000000000000^3125 ≤ 22238855820453^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086458521 2000000000 22238855820453 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212119869/400000000 : ℝ), (-1040675097/5000000000 : ℝ), (1086458521/2000000000 : ℝ)] ![(21538850513631/50000000000000 : ℝ), (12444587313731/100000000000000 : ℝ), (22238855820453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212119869/400000000 : ℝ)|^4149 ≤ (21538850513631/50000000000000 : ℝ)^3125
        have hw : |(212119869/400000000 : ℝ)|=(212119869/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040675097/5000000000 : ℝ)|^4149 ≤ (12444587313731/100000000000000 : ℝ)^3125
        have hw : |(-1040675097/5000000000 : ℝ)|=(1040675097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086458521/2000000000 : ℝ)|^4149 ≤ (22238855820453/50000000000000 : ℝ)^3125
        have hw : |(1086458521/2000000000 : ℝ)|=(1086458521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s3_6 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325749199/2500000000 : ℝ)*x 0 + (1358073103/2500000000 : ℝ)*x 1 + (-1040675181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325749199/2500000000 : ℝ)^4149 ≤ (10769425448251/25000000000000 : ℝ)^3125 := by
    have hnat : (1325749199 : ℕ)^4149*25000000000000^3125 ≤ 10769425448251^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325749199 2500000000 10769425448251 25000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358073103/2500000000 : ℝ)^4149 ≤ (11119427385721/25000000000000 : ℝ)^3125 := by
    have hnat : (1358073103 : ℕ)^4149*25000000000000^3125 ≤ 11119427385721^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358073103 2500000000 11119427385721 25000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040675181/5000000000 : ℝ)^4149 ≤ (1244458864737/10000000000000 : ℝ)^3125 := by
    have hnat : (1040675181 : ℕ)^4149*10000000000000^3125 ≤ 1244458864737^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040675181 5000000000 1244458864737 10000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325749199/2500000000 : ℝ), (1358073103/2500000000 : ℝ), (-1040675181/5000000000 : ℝ)] ![(10769425448251/25000000000000 : ℝ), (11119427385721/25000000000000 : ℝ), (1244458864737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325749199/2500000000 : ℝ)|^4149 ≤ (10769425448251/25000000000000 : ℝ)^3125
        have hw : |(1325749199/2500000000 : ℝ)|=(1325749199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358073103/2500000000 : ℝ)|^4149 ≤ (11119427385721/25000000000000 : ℝ)^3125
        have hw : |(1358073103/2500000000 : ℝ)|=(1358073103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040675181/5000000000 : ℝ)|^4149 ≤ (1244458864737/10000000000000 : ℝ)^3125
        have hw : |(-1040675181/5000000000 : ℝ)|=(1040675181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s3_7 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367443663/10000000000 : ℝ)*x 0 + (1143141639/2500000000 : ℝ)*x 1 + (2085811699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367443663/10000000000 : ℝ)^4149 ≤ (16645889272007/50000000000000 : ℝ)^3125 := by
    have hnat : (4367443663 : ℕ)^4149*50000000000000^3125 ≤ 16645889272007^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367443663 10000000000 16645889272007 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143141639/2500000000 : ℝ)^4149 ≤ (3538353964357/10000000000000 : ℝ)^3125 := by
    have hnat : (1143141639 : ℕ)^4149*10000000000000^3125 ≤ 3538353964357^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143141639 2500000000 3538353964357 10000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085811699/5000000000 : ℝ)^4149 ≤ (31324681802813/100000000000000 : ℝ)^3125 := by
    have hnat : (2085811699 : ℕ)^4149*100000000000000^3125 ≤ 31324681802813^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085811699 5000000000 31324681802813 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367443663/10000000000 : ℝ), (1143141639/2500000000 : ℝ), (2085811699/5000000000 : ℝ)] ![(16645889272007/50000000000000 : ℝ), (3538353964357/10000000000000 : ℝ), (31324681802813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367443663/10000000000 : ℝ)|^4149 ≤ (16645889272007/50000000000000 : ℝ)^3125
        have hw : |(4367443663/10000000000 : ℝ)|=(4367443663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1143141639/2500000000 : ℝ)|^4149 ≤ (3538353964357/10000000000000 : ℝ)^3125
        have hw : |(1143141639/2500000000 : ℝ)|=(1143141639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085811699/5000000000 : ℝ)|^4149 ≤ (31324681802813/100000000000000 : ℝ)^3125
        have hw : |(2085811699/5000000000 : ℝ)|=(2085811699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1105_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3323/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5261/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3713/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3323/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3323/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3323/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3323/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3323/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3323/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8899/100000 : ℝ) ^ (8297/2048 : ℝ) ≤ (553985047906409/10000000000000000000 : ℝ) := by
    have hpowers : (8899/100000 : ℝ)^8297 ≤ (553985047906409/10000000000000000000 : ℝ)^2048 := by
      have hnat : (8899 : ℕ)^8297*10000000000000000000^2048 ≤ 553985047906409^2048*100000^8297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8899 100000 553985047906409 10000000000000000000 8297 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8899/100000 : ℝ)) (X := (553985047906409/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3323/20000 : ℝ) ^ (8297/2048 : ℝ) ≤ (34754160698583447/50000000000000000000 : ℝ) := by
    have hpowers : (3323/20000 : ℝ)^8297 ≤ (34754160698583447/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3323 : ℕ)^8297*50000000000000000000^2048 ≤ 34754160698583447^2048*20000^8297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3323 20000 34754160698583447 50000000000000000000 8297 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3323/20000 : ℝ)) (X := (34754160698583447/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000553985047906409/5000000000000000000 : ℝ) ≤ (1250034184465547/1250000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (5000553985047906409/5000000000000000000 : ℝ)^2048 ≤ (1250034184465547/1250000000000000 : ℝ)^8297 := by
      have hnat : (5000553985047906409 : ℕ)^2048*1250000000000000^8297 ≤ 1250034184465547^8297*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000553985047906409 5000000000000000000 1250034184465547 1250000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250034184465547/1250000000000000 : ℝ)) (X := (5000553985047906409/5000000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12509381021484528873/12500000000000000000 : ℝ) ≤ (2000370387458269/2000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (12509381021484528873/12500000000000000000 : ℝ)^2048 ≤ (2000370387458269/2000000000000000 : ℝ)^8297 := by
      have hnat : (12509381021484528873 : ℕ)^2048*2000000000000000^8297 ≤ 2000370387458269^8297*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509381021484528873 12500000000000000000 2000370387458269 2000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000370387458269/2000000000000000 : ℝ)) (X := (12509381021484528873/12500000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25034754160698583447/25000000000000000000 : ℝ) ≤ (5001715199429157/5000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (25034754160698583447/25000000000000000000 : ℝ)^2048 ≤ (5001715199429157/5000000000000000 : ℝ)^8297 := by
      have hnat : (25034754160698583447 : ℕ)^2048*5000000000000000^8297 ≤ 5001715199429157^8297*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034754160698583447 25000000000000000000 5001715199429157 5000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001715199429157/5000000000000000 : ℝ)) (X := (25034754160698583447/25000000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(553985047906409/10000000000000000000 : ℝ) ≤ ((38567008339860185477/38580000000000000000 : ℝ)+2*(1578461566969/771600000000000 : ℝ)*(8899/100000 : ℝ))^(8297/2048 : ℝ) := by
    rw [show (38567008339860185477/38580000000000000000 : ℝ)+2*(1578461566969/771600000000000 : ℝ)*(8899/100000 : ℝ)=(1250034184465547/1250000000000000 : ℝ) by norm_num, show 1+2*(553985047906409/10000000000000000000 : ℝ)=(5000553985047906409/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34754160698583447/50000000000000000000 : ℝ)+(553985047906409/10000000000000000000 : ℝ) ≤ ((38567008339860185477/38580000000000000000 : ℝ)+(1578461566969/771600000000000 : ℝ)*((3323/20000 : ℝ)+(8899/100000 : ℝ)))^(8297/2048 : ℝ) := by
    rw [show (38567008339860185477/38580000000000000000 : ℝ)+(1578461566969/771600000000000 : ℝ)*((3323/20000 : ℝ)+(8899/100000 : ℝ))=(2000370387458269/2000000000000000 : ℝ) by norm_num, show 1+(34754160698583447/50000000000000000000 : ℝ)+(553985047906409/10000000000000000000 : ℝ)=(12509381021484528873/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34754160698583447/50000000000000000000 : ℝ) ≤ ((38567008339860185477/38580000000000000000 : ℝ)+2*(1578461566969/771600000000000 : ℝ)*(3323/20000 : ℝ))^(8297/2048 : ℝ) := by
    rw [show (38567008339860185477/38580000000000000000 : ℝ)+2*(1578461566969/771600000000000 : ℝ)*(3323/20000 : ℝ)=(5001715199429157/5000000000000000 : ℝ) by norm_num, show 1+2*(34754160698583447/50000000000000000000 : ℝ)=(25034754160698583447/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38567008339860185477/38580000000000000000 : ℝ)*(X 1 0+X 2 0)+(1578461566969/771600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (8899/100000 : ℝ)) (hi := (3323/20000 : ℝ)) (c := (38567008339860185477/38580000000000000000 : ℝ)) (alpha := (1578461566969/771600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38567008339860185477/38580000000000000000 : ℝ)*(X 0 1+X 2 1)+(1578461566969/771600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (8899/100000 : ℝ)) (hi := (3323/20000 : ℝ)) (c := (38567008339860185477/38580000000000000000 : ℝ)) (alpha := (1578461566969/771600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38567008339860185477/38580000000000000000 : ℝ)*(X 0 2+X 1 2)+(1578461566969/771600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (8899/100000 : ℝ)) (hi := (3323/20000 : ℝ)) (c := (38567008339860185477/38580000000000000000 : ℝ)) (alpha := (1578461566969/771600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-136279839/625000000 : ℝ)*X 0 0+(13582781/25000000 : ℝ)*X 0 1+(5228472837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070939797/2000000000 : ℝ)*X 1 0+(-1142584907/5000000000 : ℝ)*X 1 1+(1307118239/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338674781/2500000000 : ℝ)*X 2 0+(5228473053/10000000000 : ℝ)*X 2 1+(-2285169503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183702173/5000000000 : ℝ)*X 0 0+(521250559/1250000000 : ℝ)*X 0 1+(4574176061/10000000000 : ℝ)*X 0 2+(2183702173/5000000000 : ℝ)*X 1 0+(521250559/1250000000 : ℝ)*X 1 1+(4574176061/10000000000 : ℝ)*X 1 2+(2183702173/5000000000 : ℝ)*X 2 0+(521250559/1250000000 : ℝ)*X 2 1+(4574176061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2180497359/10000000000 : ℝ)*X 0 0+(2614644107/5000000000 : ℝ)*X 0 1+(1358073099/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212119869/400000000 : ℝ)*X 1 0+(-1040675097/5000000000 : ℝ)*X 1 1+(1086458521/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325749199/2500000000 : ℝ)*X 2 0+(1358073103/2500000000 : ℝ)*X 2 1+(-1040675181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367443663/10000000000 : ℝ)*X 0 0+(1143141639/2500000000 : ℝ)*X 0 1+(2085811699/5000000000 : ℝ)*X 0 2+(4367443663/10000000000 : ℝ)*X 1 0+(1143141639/2500000000 : ℝ)*X 1 1+(2085811699/5000000000 : ℝ)*X 1 2+(4367443663/10000000000 : ℝ)*X 2 0+(1143141639/2500000000 : ℝ)*X 2 1+(2085811699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1619922450033850673418588147/321500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1515904933/100000000000000 : ℝ)*(base19) + (142247419/10000000000000 : ℝ)*(base23) + (7372157/6250000000000 : ℝ)*(lower2) + (25743569/50000000000000 : ℝ)*(upper3) + (224111687/100000000000000 : ℝ)*(upper5) + (1840231611605763/50000000000000 : ℝ)*(major0) + (1840231611605763/50000000000000 : ℝ)*(major1) + (1840231611605763/50000000000000 : ℝ)*(major2) + (2443333923123661/50000000000000 : ℝ)*(sp0) + (2443351072745351/50000000000000 : ℝ)*(sp1) + (977340447784289/20000000000000 : ℝ)*(sp2) + (1237105056821419/50000000000000 : ℝ)*(sp3) + (4476893539/12500000000000 : ℝ)*(sp4) + (6251714967/50000000000000 : ℝ)*(sp7) + (2474222617072773/100000000000000 : ℝ)*(f.failure) + (2443351830697817/50000000000000 : ℝ)*(f.sum) + (29136266292229/6430000000000000000000000000 : ℝ)*base65 + (6445501686689151317/643000000000000000000000000000000 : ℝ)*base67 + (8005947906045151317/643000000000000000000000000000000 : ℝ)*base69 + (2540386985653151317/643000000000000000000000000000000 : ℝ)*base71 + (58679713028289/6430000000000000000000000000 : ℝ)*base73 + (1315129715467151317/643000000000000000000000000000000 : ℝ)*base75 + (5163841961123151317/643000000000000000000000000000000 : ℝ)*base77 + (4042138713758151317/643000000000000000000000000000000 : ℝ)*base79 + (23027834700999/6430000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (29362689/10000000000000000000000 : ℝ)*base90 + (29362689/10000000000000000000000 : ℝ)*base92 + (29362689/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4488825991957189519538272013/643000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39413847/3125000000000 : ℝ)*(base19) + (789237957/50000000000000 : ℝ)*(base23) + (383129/200000000000 : ℝ)*(upper3) + (7430999/6250000000000 : ℝ)*(lower4) + (82817871/100000000000000 : ℝ)*(upper5) + (3710061057701123/100000000000000 : ℝ)*(major0) + (3710061057701123/100000000000000 : ℝ)*(major1) + (3710061057701123/100000000000000 : ℝ)*(major2) + (23917609873/100000000000000 : ℝ)*(sp1) + (104275797/390625000000 : ℝ)*(sp2) + (4926001870362237/100000000000000 : ℝ)*(sp4) + (4925976691509261/100000000000000 : ℝ)*(sp5) + (1231493399320573/25000000000000 : ℝ)*(sp6) + (1247060006168887/50000000000000 : ℝ)*(sp7) + (1247060006168887/50000000000000 : ℝ)*(f.failure) + (4926001870362237/100000000000000 : ℝ)*(f.sum) + (106638079438367/38580000000000000000000000000 : ℝ)*base65 + (14814671364875459329/3858000000000000000000000000000000 : ℝ)*base68 + (15357587805311459329/3858000000000000000000000000000000 : ℝ)*base70 + (22408813464215459329/3858000000000000000000000000000000 : ℝ)*base72 + (74872024668853/38580000000000000000000000000 : ℝ)*base74 + (15889064500289459329/3858000000000000000000000000000000 : ℝ)*base76 + (12731233695875459329/3858000000000000000000000000000000 : ℝ)*base78 + (48054980546831459329/3858000000000000000000000000000000 : ℝ)*base80 + (1699855484027/38580000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (22872309/5000000000000000000000 : ℝ)*base89 + (22872309/5000000000000000000000 : ℝ)*base91 + (22872309/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1105_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3323/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3713/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1105_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1105_s4_0 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-545947309/2500000000 : ℝ)*x 0 + (1350932617/2500000000 : ℝ)*x 1 + (5255689951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545947309/2500000000 : ℝ)^4149 ≤ (13264268060887/100000000000000 : ℝ)^3125 := by
    have hnat : (545947309 : ℕ)^4149*100000000000000^3125 ≤ 13264268060887^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545947309 2500000000 13264268060887 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350932617/2500000000 : ℝ)^4149 ≤ (44167492445531/100000000000000 : ℝ)^3125 := by
    have hnat : (1350932617 : ℕ)^4149*100000000000000^3125 ≤ 44167492445531^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350932617 2500000000 44167492445531 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255689951/10000000000 : ℝ)^4149 ≤ (42568239480191/100000000000000 : ℝ)^3125 := by
    have hnat : (5255689951 : ℕ)^4149*100000000000000^3125 ≤ 42568239480191^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255689951 10000000000 42568239480191 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545947309/2500000000 : ℝ), (1350932617/2500000000 : ℝ), (5255689951/10000000000 : ℝ)] ![(13264268060887/100000000000000 : ℝ), (44167492445531/100000000000000 : ℝ), (42568239480191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545947309/2500000000 : ℝ)|^4149 ≤ (13264268060887/100000000000000 : ℝ)^3125
        have hw : |(-545947309/2500000000 : ℝ)|=(545947309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350932617/2500000000 : ℝ)|^4149 ≤ (44167492445531/100000000000000 : ℝ)^3125
        have hw : |(1350932617/2500000000 : ℝ)|=(1350932617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255689951/10000000000 : ℝ)|^4149 ≤ (42568239480191/100000000000000 : ℝ)^3125
        have hw : |(5255689951/10000000000 : ℝ)|=(5255689951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s4_1 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069478191/2000000000 : ℝ)*x 0 + (-112952561/500000000 : ℝ)*x 1 + (2627845163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069478191/2000000000 : ℝ)^4149 ≤ (5444644144961/12500000000000 : ℝ)^3125 := by
    have hnat : (1069478191 : ℕ)^4149*12500000000000^3125 ≤ 5444644144961^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069478191 2000000000 5444644144961 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112952561/500000000 : ℝ)^4149 ≤ (13874603312441/100000000000000 : ℝ)^3125 := by
    have hnat : (112952561 : ℕ)^4149*100000000000000^3125 ≤ 13874603312441^3125*500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112952561 500000000 13874603312441 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627845163/5000000000 : ℝ)^4149 ≤ (42568243512749/100000000000000 : ℝ)^3125 := by
    have hnat : (2627845163 : ℕ)^4149*100000000000000^3125 ≤ 42568243512749^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627845163 5000000000 42568243512749 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069478191/2000000000 : ℝ), (-112952561/500000000 : ℝ), (2627845163/5000000000 : ℝ)] ![(5444644144961/12500000000000 : ℝ), (13874603312441/100000000000000 : ℝ), (42568243512749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069478191/2000000000 : ℝ)|^4149 ≤ (5444644144961/12500000000000 : ℝ)^3125
        have hw : |(1069478191/2000000000 : ℝ)|=(1069478191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112952561/500000000 : ℝ)|^4149 ≤ (13874603312441/100000000000000 : ℝ)^3125
        have hw : |(-112952561/500000000 : ℝ)|=(112952561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627845163/5000000000 : ℝ)|^4149 ≤ (42568243512749/100000000000000 : ℝ)^3125
        have hw : |(2627845163/5000000000 : ℝ)|=(2627845163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s4_2 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673695343/5000000000 : ℝ)*x 0 + (1313922599/2500000000 : ℝ)*x 1 + (-451810297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673695343/5000000000 : ℝ)^4149 ≤ (43557150250557/100000000000000 : ℝ)^3125 := by
    have hnat : (2673695343 : ℕ)^4149*100000000000000^3125 ≤ 43557150250557^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673695343 5000000000 43557150250557 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313922599/2500000000 : ℝ)^4149 ≤ (21284122132747/50000000000000 : ℝ)^3125 := by
    have hnat : (1313922599 : ℕ)^4149*50000000000000^3125 ≤ 21284122132747^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313922599 2500000000 21284122132747 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451810297/2000000000 : ℝ)^4149 ≤ (1734325684167/12500000000000 : ℝ)^3125 := by
    have hnat : (451810297 : ℕ)^4149*12500000000000^3125 ≤ 1734325684167^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451810297 2000000000 1734325684167 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673695343/5000000000 : ℝ), (1313922599/2500000000 : ℝ), (-451810297/2000000000 : ℝ)] ![(43557150250557/100000000000000 : ℝ), (21284122132747/50000000000000 : ℝ), (1734325684167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673695343/5000000000 : ℝ)|^4149 ≤ (43557150250557/100000000000000 : ℝ)^3125
        have hw : |(2673695343/5000000000 : ℝ)|=(2673695343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313922599/2500000000 : ℝ)|^4149 ≤ (21284122132747/50000000000000 : ℝ)^3125
        have hw : |(1313922599/2500000000 : ℝ)|=(1313922599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451810297/2000000000 : ℝ)|^4149 ≤ (1734325684167/12500000000000 : ℝ)^3125
        have hw : |(-451810297/2000000000 : ℝ)|=(451810297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s4_3 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369379159/10000000000 : ℝ)*x 0 + (1056409853/2500000000 : ℝ)*x 1 + (903605237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369379159/10000000000 : ℝ)^4149 ≤ (4163921025543/12500000000000 : ℝ)^3125 := by
    have hnat : (4369379159 : ℕ)^4149*12500000000000^3125 ≤ 4163921025543^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369379159 10000000000 4163921025543 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056409853/2500000000 : ℝ)^4149 ≤ (31864335595929/100000000000000 : ℝ)^3125 := by
    have hnat : (1056409853 : ℕ)^4149*100000000000000^3125 ≤ 31864335595929^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056409853 2500000000 31864335595929 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903605237/2000000000 : ℝ)^4149 ≤ (17412148093931/50000000000000 : ℝ)^3125 := by
    have hnat : (903605237 : ℕ)^4149*50000000000000^3125 ≤ 17412148093931^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903605237 2000000000 17412148093931 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369379159/10000000000 : ℝ), (1056409853/2500000000 : ℝ), (903605237/2000000000 : ℝ)] ![(4163921025543/12500000000000 : ℝ), (31864335595929/100000000000000 : ℝ), (17412148093931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369379159/10000000000 : ℝ)|^4149 ≤ (4163921025543/12500000000000 : ℝ)^3125
        have hw : |(4369379159/10000000000 : ℝ)|=(4369379159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056409853/2500000000 : ℝ)|^4149 ≤ (31864335595929/100000000000000 : ℝ)^3125
        have hw : |(1056409853/2500000000 : ℝ)|=(1056409853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903605237/2000000000 : ℝ)|^4149 ≤ (17412148093931/50000000000000 : ℝ)^3125
        have hw : |(903605237/2000000000 : ℝ)|=(903605237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s4_4 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183796541/10000000000 : ℝ)*x 0 + (5256117451/10000000000 : ℝ)*x 1 + (2701650701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183796541/10000000000 : ℝ)^4149 ≤ (1658040871317/12500000000000 : ℝ)^3125 := by
    have hnat : (2183796541 : ℕ)^4149*12500000000000^3125 ≤ 1658040871317^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183796541 10000000000 1658040871317 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256117451/10000000000 : ℝ)^4149 ≤ (42572836657687/100000000000000 : ℝ)^3125 := by
    have hnat : (5256117451 : ℕ)^4149*100000000000000^3125 ≤ 42572836657687^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256117451 10000000000 42572836657687 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701650701/5000000000 : ℝ)^4149 ≤ (5520354545027/12500000000000 : ℝ)^3125 := by
    have hnat : (2701650701 : ℕ)^4149*12500000000000^3125 ≤ 5520354545027^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701650701 5000000000 5520354545027 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183796541/10000000000 : ℝ), (5256117451/10000000000 : ℝ), (2701650701/5000000000 : ℝ)] ![(1658040871317/12500000000000 : ℝ), (42572836657687/100000000000000 : ℝ), (5520354545027/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183796541/10000000000 : ℝ)|^4149 ≤ (1658040871317/12500000000000 : ℝ)^3125
        have hw : |(-2183796541/10000000000 : ℝ)|=(2183796541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256117451/10000000000 : ℝ)|^4149 ≤ (42572836657687/100000000000000 : ℝ)^3125
        have hw : |(5256117451/10000000000 : ℝ)|=(5256117451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701650701/5000000000 : ℝ)|^4149 ≤ (5520354545027/12500000000000 : ℝ)^3125
        have hw : |(2701650701/5000000000 : ℝ)|=(2701650701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s4_5 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530999039/1000000000 : ℝ)*x 0 + (-211144039/1000000000 : ℝ)*x 1 + (675412697/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530999039/1000000000 : ℝ)^4149 ≤ (539414309569/1250000000000 : ℝ)^3125 := by
    have hnat : (530999039 : ℕ)^4149*1250000000000^3125 ≤ 539414309569^3125*1000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530999039 1000000000 539414309569 1250000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211144039/1000000000 : ℝ)^4149 ≤ (253680339363/2000000000000 : ℝ)^3125 := by
    have hnat : (211144039 : ℕ)^4149*2000000000000^3125 ≤ 253680339363^3125*1000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211144039 1000000000 253680339363 2000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675412697/1250000000 : ℝ)^4149 ≤ (44162838248383/100000000000000 : ℝ)^3125 := by
    have hnat : (675412697 : ℕ)^4149*100000000000000^3125 ≤ 44162838248383^3125*1250000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675412697 1250000000 44162838248383 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530999039/1000000000 : ℝ), (-211144039/1000000000 : ℝ), (675412697/1250000000 : ℝ)] ![(539414309569/1250000000000 : ℝ), (253680339363/2000000000000 : ℝ), (44162838248383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530999039/1000000000 : ℝ)|^4149 ≤ (539414309569/1250000000000 : ℝ)^3125
        have hw : |(530999039/1000000000 : ℝ)|=(530999039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211144039/1000000000 : ℝ)|^4149 ≤ (253680339363/2000000000000 : ℝ)^3125
        have hw : |(-211144039/1000000000 : ℝ)|=(211144039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675412697/1250000000 : ℝ)|^4149 ≤ (44162838248383/100000000000000 : ℝ)^3125
        have hw : |(675412697/1250000000 : ℝ)|=(675412697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s4_6 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061998117/2000000000 : ℝ)*x 0 + (2701650707/5000000000 : ℝ)*x 1 + (-2111440347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061998117/2000000000 : ℝ)^4149 ≤ (1726125874781/4000000000000 : ℝ)^3125 := by
    have hnat : (1061998117 : ℕ)^4149*4000000000000^3125 ≤ 1726125874781^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061998117 2000000000 1726125874781 4000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701650707/5000000000 : ℝ)^4149 ≤ (22081418245217/50000000000000 : ℝ)^3125 := by
    have hnat : (2701650707 : ℕ)^4149*50000000000000^3125 ≤ 22081418245217^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701650707 5000000000 22081418245217 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111440347/10000000000 : ℝ)^4149 ≤ (12684016625193/100000000000000 : ℝ)^3125 := by
    have hnat : (2111440347 : ℕ)^4149*100000000000000^3125 ≤ 12684016625193^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111440347 10000000000 12684016625193 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061998117/2000000000 : ℝ), (2701650707/5000000000 : ℝ), (-2111440347/10000000000 : ℝ)] ![(1726125874781/4000000000000 : ℝ), (22081418245217/50000000000000 : ℝ), (12684016625193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061998117/2000000000 : ℝ)|^4149 ≤ (1726125874781/4000000000000 : ℝ)^3125
        have hw : |(1061998117/2000000000 : ℝ)|=(1061998117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701650707/5000000000 : ℝ)|^4149 ≤ (22081418245217/50000000000000 : ℝ)^3125
        have hw : |(2701650707/5000000000 : ℝ)|=(2701650707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111440347/10000000000 : ℝ)|^4149 ≤ (12684016625193/100000000000000 : ℝ)^3125
        have hw : |(-2111440347/10000000000 : ℝ)|=(2111440347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s4_7 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369394047/10000000000 : ℝ)*x 0 + (903436377/2000000000 : ℝ)*x 1 + (105662183/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369394047/10000000000 : ℝ)^4149 ≤ (16655759450351/50000000000000 : ℝ)^3125 := by
    have hnat : (4369394047 : ℕ)^4149*50000000000000^3125 ≤ 16655759450351^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369394047 10000000000 16655759450351 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903436377/2000000000 : ℝ)^4149 ≤ (34815656252189/100000000000000 : ℝ)^3125 := by
    have hnat : (903436377 : ℕ)^4149*100000000000000^3125 ≤ 34815656252189^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903436377 2000000000 34815656252189 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105662183/250000000 : ℝ)^4149 ≤ (31872824836791/100000000000000 : ℝ)^3125 := by
    have hnat : (105662183 : ℕ)^4149*100000000000000^3125 ≤ 31872824836791^3125*250000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105662183 250000000 31872824836791 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369394047/10000000000 : ℝ), (903436377/2000000000 : ℝ), (105662183/250000000 : ℝ)] ![(16655759450351/50000000000000 : ℝ), (34815656252189/100000000000000 : ℝ), (31872824836791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369394047/10000000000 : ℝ)|^4149 ≤ (16655759450351/50000000000000 : ℝ)^3125
        have hw : |(4369394047/10000000000 : ℝ)|=(4369394047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903436377/2000000000 : ℝ)|^4149 ≤ (34815656252189/100000000000000 : ℝ)^3125
        have hw : |(903436377/2000000000 : ℝ)|=(903436377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105662183/250000000 : ℝ)|^4149 ≤ (31872824836791/100000000000000 : ℝ)^3125
        have hw : |(105662183/250000000 : ℝ)|=(105662183/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1105_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3713/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11103/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3713/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5261/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3713/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5261/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3713/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5261/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3713/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5261/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3713/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5261/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3713/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5261/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5261/50000 : ℝ) ^ (8297/2048 : ℝ) ≤ (2184170935037463/20000000000000000000 : ℝ) := by
    have hpowers : (5261/50000 : ℝ)^8297 ≤ (2184170935037463/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5261 : ℕ)^8297*20000000000000000000^2048 ≤ 2184170935037463^2048*50000^8297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5261 50000 2184170935037463 20000000000000000000 8297 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5261/50000 : ℝ)) (X := (2184170935037463/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3713/25000 : ℝ) ^ (8297/2048 : ℝ) ≤ (44124273143154979/100000000000000000000 : ℝ) := by
    have hpowers : (3713/25000 : ℝ)^8297 ≤ (44124273143154979/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3713 : ℕ)^8297*100000000000000000000^2048 ≤ 44124273143154979^2048*25000^8297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3713 25000 44124273143154979 100000000000000000000 8297 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3713/25000 : ℝ)) (X := (44124273143154979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002184170935037463/10000000000000000000 : ℝ) ≤ (5000269544063763/5000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (10002184170935037463/10000000000000000000 : ℝ)^2048 ≤ (5000269544063763/5000000000000000 : ℝ)^8297 := by
      have hnat : (10002184170935037463 : ℕ)^2048*5000000000000000^8297 ≤ 5000269544063763^8297*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002184170935037463 10000000000000000000 5000269544063763 5000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269544063763/5000000000000000 : ℝ)) (X := (10002184170935037463/10000000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027522563909171147/50000000000000000000 : ℝ) ≤ (5000679215746559/5000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (50027522563909171147/50000000000000000000 : ℝ)^2048 ≤ (5000679215746559/5000000000000000 : ℝ)^8297 := by
      have hnat : (50027522563909171147 : ℕ)^2048*5000000000000000^8297 ≤ 5000679215746559^8297*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027522563909171147 50000000000000000000 5000679215746559 5000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000679215746559/5000000000000000 : ℝ)) (X := (50027522563909171147/50000000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044124273143154979/50000000000000000000 : ℝ) ≤ (1000217777485871/1000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (50044124273143154979/50000000000000000000 : ℝ)^2048 ≤ (1000217777485871/1000000000000000 : ℝ)^8297 := by
      have hnat : (50044124273143154979 : ℕ)^2048*1000000000000000^8297 ≤ 1000217777485871^8297*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044124273143154979 50000000000000000000 1000217777485871 1000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000217777485871/1000000000000000 : ℝ)) (X := (50044124273143154979/50000000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2184170935037463/20000000000000000000 : ℝ) ≤ ((10821272997451667383/10825000000000000000 : ℝ)+2*(102417920699/54125000000000 : ℝ)*(5261/50000 : ℝ))^(8297/2048 : ℝ) := by
    rw [show (10821272997451667383/10825000000000000000 : ℝ)+2*(102417920699/54125000000000 : ℝ)*(5261/50000 : ℝ)=(5000269544063763/5000000000000000 : ℝ) by norm_num, show 1+2*(2184170935037463/20000000000000000000 : ℝ)=(10002184170935037463/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44124273143154979/100000000000000000000 : ℝ)+(2184170935037463/20000000000000000000 : ℝ) ≤ ((10821272997451667383/10825000000000000000 : ℝ)+(102417920699/54125000000000 : ℝ)*((3713/25000 : ℝ)+(5261/50000 : ℝ)))^(8297/2048 : ℝ) := by
    rw [show (10821272997451667383/10825000000000000000 : ℝ)+(102417920699/54125000000000 : ℝ)*((3713/25000 : ℝ)+(5261/50000 : ℝ))=(5000679215746559/5000000000000000 : ℝ) by norm_num, show 1+(44124273143154979/100000000000000000000 : ℝ)+(2184170935037463/20000000000000000000 : ℝ)=(50027522563909171147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44124273143154979/100000000000000000000 : ℝ) ≤ ((10821272997451667383/10825000000000000000 : ℝ)+2*(102417920699/54125000000000 : ℝ)*(3713/25000 : ℝ))^(8297/2048 : ℝ) := by
    rw [show (10821272997451667383/10825000000000000000 : ℝ)+2*(102417920699/54125000000000 : ℝ)*(3713/25000 : ℝ)=(1000217777485871/1000000000000000 : ℝ) by norm_num, show 1+2*(44124273143154979/100000000000000000000 : ℝ)=(50044124273143154979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10821272997451667383/10825000000000000000 : ℝ)*(X 1 0+X 2 0)+(102417920699/54125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (3713/25000 : ℝ)) (c := (10821272997451667383/10825000000000000000 : ℝ)) (alpha := (102417920699/54125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10821272997451667383/10825000000000000000 : ℝ)*(X 0 1+X 2 1)+(102417920699/54125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (3713/25000 : ℝ)) (c := (10821272997451667383/10825000000000000000 : ℝ)) (alpha := (102417920699/54125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10821272997451667383/10825000000000000000 : ℝ)*(X 0 2+X 1 2)+(102417920699/54125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (3713/25000 : ℝ)) (c := (10821272997451667383/10825000000000000000 : ℝ)) (alpha := (102417920699/54125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-545947309/2500000000 : ℝ)*X 0 0+(1350932617/2500000000 : ℝ)*X 0 1+(5255689951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069478191/2000000000 : ℝ)*X 1 0+(-112952561/500000000 : ℝ)*X 1 1+(2627845163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673695343/5000000000 : ℝ)*X 2 0+(1313922599/2500000000 : ℝ)*X 2 1+(-451810297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369379159/10000000000 : ℝ)*X 0 0+(1056409853/2500000000 : ℝ)*X 0 1+(903605237/2000000000 : ℝ)*X 0 2+(4369379159/10000000000 : ℝ)*X 1 0+(1056409853/2500000000 : ℝ)*X 1 1+(903605237/2000000000 : ℝ)*X 1 2+(4369379159/10000000000 : ℝ)*X 2 0+(1056409853/2500000000 : ℝ)*X 2 1+(903605237/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183796541/10000000000 : ℝ)*X 0 0+(5256117451/10000000000 : ℝ)*X 0 1+(2701650701/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530999039/1000000000 : ℝ)*X 1 0+(-211144039/1000000000 : ℝ)*X 1 1+(675412697/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061998117/2000000000 : ℝ)*X 2 0+(2701650707/5000000000 : ℝ)*X 2 1+(-2111440347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369394047/10000000000 : ℝ)*X 0 0+(903436377/2000000000 : ℝ)*X 0 1+(105662183/250000000 : ℝ)*X 0 2+(4369394047/10000000000 : ℝ)*X 1 0+(903436377/2000000000 : ℝ)*X 1 1+(105662183/250000000 : ℝ)*X 1 2+(4369394047/10000000000 : ℝ)*X 2 0+(903436377/2000000000 : ℝ)*X 2 1+(105662183/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (556710145264077694309182423/135312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (409353999/20000000000000 : ℝ)*(base19) + (754144373/50000000000000 : ℝ)*(base23) + (33128109/100000000000000 : ℝ)*(upper2) + (115813029/20000000000000 : ℝ)*(upper3) + (69682547/50000000000000 : ℝ)*(upper4) + (1271900400684373/25000000000000 : ℝ)*(major0) + (1271900400684373/25000000000000 : ℝ)*(major1) + (1271900400684373/25000000000000 : ℝ)*(major2) + (3377488012568771/50000000000000 : ℝ)*(sp0) + (3377508847215811/50000000000000 : ℝ)*(sp1) + (844377279114109/12500000000000 : ℝ)*(sp2) + (1710075242011823/50000000000000 : ℝ)*(sp3) + (10929016019/25000000000000 : ℝ)*(sp4) + (16421553937/50000000000000 : ℝ)*(sp7) + (5344036448643/156250000000 : ℝ)*(f.failure) + (6755019741201617/100000000000000 : ℝ)*(f.sum) + (36634907420667/2706250000000000000000000000 : ℝ)*base66 + (639408998918555859/270625000000000000000000000000000 : ℝ)*base67 + (611469711162694141/270625000000000000000000000000000 : ℝ)*base70 + (40088224716055859/270625000000000000000000000000000 : ℝ)*base71 + (27467935634509/5412500000000000000000000000 : ℝ)*base74 + (3404872185166055859/270625000000000000000000000000000 : ℝ)*base75 + (2945861151412694141/270625000000000000000000000000000 : ℝ)*base78 + (4974454157956055859/270625000000000000000000000000000 : ℝ)*base79 + (20689285280059/5412500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (144401/15625000000000000000 : ℝ)*base89 + (144401/15625000000000000000 : ℝ)*base91 + (144401/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144285634756792340056161861/16914062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1496358263/100000000000000 : ℝ)*(base19) + (221221657/12500000000000 : ℝ)*(base23) + (23053749/12500000000000 : ℝ)*(upper3) + (8401419/50000000000000 : ℝ)*(lower4) + (340858511/100000000000000 : ℝ)*(upper5) + (319820710574147/6250000000000 : ℝ)*(major0) + (319820710574147/6250000000000 : ℝ)*(major1) + (319820710574147/6250000000000 : ℝ)*(major2) + (42111989021/100000000000000 : ℝ)*(sp1) + (20507174187/50000000000000 : ℝ)*(sp2) + (6794227490943427/100000000000000 : ℝ)*(sp4) + (424636492662259/6250000000000 : ℝ)*(sp5) + (3397092353410899/50000000000000 : ℝ)*(sp6) + (1720017481539413/50000000000000 : ℝ)*(sp7) + (1720017481539413/50000000000000 : ℝ)*(f.failure) + (6794227490943427/100000000000000 : ℝ)*(f.sum) + (14189133572183/10825000000000000000000000000 : ℝ)*base66 + (647654067345578551/67656250000000000000000000000000 : ℝ)*base67 + (671783033818859801/67656250000000000000000000000000 : ℝ)*base69 + (322374077787233949/67656250000000000000000000000000 : ℝ)*base72 + (29651478017721/5412500000000000000000000000 : ℝ)*base73 + (758190271961359801/67656250000000000000000000000000 : ℝ)*base75 + (274598967241452699/67656250000000000000000000000000 : ℝ)*base78 + (451383698866359801/67656250000000000000000000000000 : ℝ)*base79 + (3974751460337/676562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4824209/5000000000000000000000 : ℝ)*base90 + (4824209/5000000000000000000000 : ℝ)*base92 + (4824209/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1105_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3713/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1105_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1105_s5_0 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17476101/80000000 : ℝ)*x 0 + (5395906317/10000000000 : ℝ)*x 1 + (1315759893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17476101/80000000 : ℝ)^4149 ≤ (3317525498517/25000000000000 : ℝ)^3125 := by
    have hnat : (17476101 : ℕ)^4149*25000000000000^3125 ≤ 3317525498517^3125*80000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17476101 80000000 3317525498517 25000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395906317/10000000000 : ℝ)^4149 ≤ (2204130316803/5000000000000 : ℝ)^3125 := by
    have hnat : (5395906317 : ℕ)^4149*5000000000000^3125 ≤ 2204130316803^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395906317 10000000000 2204130316803 5000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315759893/2500000000 : ℝ)^4149 ≤ (68235666633/160000000000 : ℝ)^3125 := by
    have hnat : (1315759893 : ℕ)^4149*160000000000^3125 ≤ 68235666633^3125*2500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315759893 2500000000 68235666633 160000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17476101/80000000 : ℝ), (5395906317/10000000000 : ℝ), (1315759893/2500000000 : ℝ)] ![(3317525498517/25000000000000 : ℝ), (2204130316803/5000000000000 : ℝ), (68235666633/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17476101/80000000 : ℝ)|^4149 ≤ (3317525498517/25000000000000 : ℝ)^3125
        have hw : |(-17476101/80000000 : ℝ)|=(17476101/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395906317/10000000000 : ℝ)|^4149 ≤ (2204130316803/5000000000000 : ℝ)^3125
        have hw : |(5395906317/10000000000 : ℝ)|=(5395906317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315759893/2500000000 : ℝ)|^4149 ≤ (68235666633/160000000000 : ℝ)^3125
        have hw : |(1315759893/2500000000 : ℝ)|=(1315759893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s5_1 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672717643/5000000000 : ℝ)*x 0 + (-450389411/2000000000 : ℝ)*x 1 + (526303959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672717643/5000000000 : ℝ)^4149 ≤ (43536004624663/100000000000000 : ℝ)^3125 := by
    have hnat : (2672717643 : ℕ)^4149*100000000000000^3125 ≤ 43536004624663^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672717643 5000000000 43536004624663 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450389411/2000000000 : ℝ)^4149 ≤ (13816703524927/100000000000000 : ℝ)^3125 := by
    have hnat : (450389411 : ℕ)^4149*100000000000000^3125 ≤ 13816703524927^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450389411 2000000000 13816703524927 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526303959/1000000000 : ℝ)^4149 ≤ (42647291839277/100000000000000 : ℝ)^3125 := by
    have hnat : (526303959 : ℕ)^4149*100000000000000^3125 ≤ 42647291839277^3125*1000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526303959 1000000000 42647291839277 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672717643/5000000000 : ℝ), (-450389411/2000000000 : ℝ), (526303959/1000000000 : ℝ)] ![(43536004624663/100000000000000 : ℝ), (13816703524927/100000000000000 : ℝ), (42647291839277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672717643/5000000000 : ℝ)|^4149 ≤ (43536004624663/100000000000000 : ℝ)^3125
        have hw : |(2672717643/5000000000 : ℝ)|=(2672717643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450389411/2000000000 : ℝ)|^4149 ≤ (13816703524927/100000000000000 : ℝ)^3125
        have hw : |(-450389411/2000000000 : ℝ)|=(450389411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526303959/1000000000 : ℝ)|^4149 ≤ (42647291839277/100000000000000 : ℝ)^3125
        have hw : |(526303959/1000000000 : ℝ)|=(526303959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s5_2 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345435319/10000000000 : ℝ)*x 0 + (2631519793/5000000000 : ℝ)*x 1 + (-2251947017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345435319/10000000000 : ℝ)^4149 ≤ (43536004981503/100000000000000 : ℝ)^3125 := by
    have hnat : (5345435319 : ℕ)^4149*100000000000000^3125 ≤ 43536004981503^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345435319 10000000000 43536004981503 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631519793/5000000000 : ℝ)^4149 ≤ (42647291796243/100000000000000 : ℝ)^3125 := by
    have hnat : (2631519793 : ℕ)^4149*100000000000000^3125 ≤ 42647291796243^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631519793 5000000000 42647291796243 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251947017/10000000000 : ℝ)^4149 ≤ (6908351607691/50000000000000 : ℝ)^3125 := by
    have hnat : (2251947017 : ℕ)^4149*50000000000000^3125 ≤ 6908351607691^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251947017 10000000000 6908351607691 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345435319/10000000000 : ℝ), (2631519793/5000000000 : ℝ), (-2251947017/10000000000 : ℝ)] ![(43536004981503/100000000000000 : ℝ), (42647291796243/100000000000000 : ℝ), (6908351607691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345435319/10000000000 : ℝ)|^4149 ≤ (43536004981503/100000000000000 : ℝ)^3125
        have hw : |(5345435319/10000000000 : ℝ)|=(5345435319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631519793/5000000000 : ℝ)|^4149 ≤ (42647291796243/100000000000000 : ℝ)^3125
        have hw : |(2631519793/5000000000 : ℝ)|=(2631519793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251947017/10000000000 : ℝ)|^4149 ≤ (6908351607691/50000000000000 : ℝ)^3125
        have hw : |(-2251947017/10000000000 : ℝ)|=(2251947017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s5_3 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369800733/10000000000 : ℝ)*x 0 + (2120284439/5000000000 : ℝ)*x 1 + (225149341/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369800733/10000000000 : ℝ)^4149 ≤ (832890886051/2500000000000 : ℝ)^3125 := by
    have hnat : (4369800733 : ℕ)^4149*2500000000000^3125 ≤ 832890886051^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369800733 10000000000 832890886051 2500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120284439/5000000000 : ℝ)^4149 ≤ (32013890701407/100000000000000 : ℝ)^3125 := by
    have hnat : (2120284439 : ℕ)^4149*100000000000000^3125 ≤ 32013890701407^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120284439 5000000000 32013890701407 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225149341/500000000 : ℝ)^4149 ≤ (34670473845951/100000000000000 : ℝ)^3125 := by
    have hnat : (225149341 : ℕ)^4149*100000000000000^3125 ≤ 34670473845951^3125*500000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225149341 500000000 34670473845951 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369800733/10000000000 : ℝ), (2120284439/5000000000 : ℝ), (225149341/500000000 : ℝ)] ![(832890886051/2500000000000 : ℝ), (32013890701407/100000000000000 : ℝ), (34670473845951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369800733/10000000000 : ℝ)|^4149 ≤ (832890886051/2500000000000 : ℝ)^3125
        have hw : |(4369800733/10000000000 : ℝ)|=(4369800733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120284439/5000000000 : ℝ)|^4149 ≤ (32013890701407/100000000000000 : ℝ)^3125
        have hw : |(2120284439/5000000000 : ℝ)|=(2120284439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225149341/500000000 : ℝ)|^4149 ≤ (34670473845951/100000000000000 : ℝ)^3125
        have hw : |(225149341/500000000 : ℝ)|=(225149341/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s5_4 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092258797/5000000000 : ℝ)*x 0 + (1052676869/2000000000 : ℝ)*x 1 + (674445081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092258797/5000000000 : ℝ)^4149 ≤ (106161136559/800000000000 : ℝ)^3125 := by
    have hnat : (1092258797 : ℕ)^4149*800000000000^3125 ≤ 106161136559^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092258797 5000000000 106161136559 800000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052676869/2000000000 : ℝ)^4149 ≤ (8530200179189/20000000000000 : ℝ)^3125 := by
    have hnat : (1052676869 : ℕ)^4149*20000000000000^3125 ≤ 8530200179189^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052676869 2000000000 8530200179189 20000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674445081/1250000000 : ℝ)^4149 ≤ (44078857019147/100000000000000 : ℝ)^3125 := by
    have hnat : (674445081 : ℕ)^4149*100000000000000^3125 ≤ 44078857019147^3125*1250000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674445081 1250000000 44078857019147 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092258797/5000000000 : ℝ), (1052676869/2000000000 : ℝ), (674445081/1250000000 : ℝ)] ![(106161136559/800000000000 : ℝ), (8530200179189/20000000000000 : ℝ), (44078857019147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092258797/5000000000 : ℝ)|^4149 ≤ (106161136559/800000000000 : ℝ)^3125
        have hw : |(-1092258797/5000000000 : ℝ)|=(1092258797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052676869/2000000000 : ℝ)|^4149 ≤ (8530200179189/20000000000000 : ℝ)^3125
        have hw : |(1052676869/2000000000 : ℝ)|=(1052676869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674445081/1250000000 : ℝ)|^4149 ≤ (44078857019147/100000000000000 : ℝ)^3125
        have hw : |(674445081/1250000000 : ℝ)|=(674445081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s5_5 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311867161/10000000000 : ℝ)*x 0 + (-423885223/2000000000 : ℝ)*x 1 + (5395560517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311867161/10000000000 : ℝ)^4149 ≤ (5396674482843/12500000000000 : ℝ)^3125 := by
    have hnat : (5311867161 : ℕ)^4149*12500000000000^3125 ≤ 5396674482843^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311867161 10000000000 5396674482843 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423885223/2000000000 : ℝ)^4149 ≤ (6373874264747/50000000000000 : ℝ)^3125 := by
    have hnat : (423885223 : ℕ)^4149*50000000000000^3125 ≤ 6373874264747^3125*2000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423885223 2000000000 6373874264747 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395560517/10000000000 : ℝ)^4149 ≤ (5509856949783/12500000000000 : ℝ)^3125 := by
    have hnat : (5395560517 : ℕ)^4149*12500000000000^3125 ≤ 5509856949783^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395560517 10000000000 5509856949783 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311867161/10000000000 : ℝ), (-423885223/2000000000 : ℝ), (5395560517/10000000000 : ℝ)] ![(5396674482843/12500000000000 : ℝ), (6373874264747/50000000000000 : ℝ), (5509856949783/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311867161/10000000000 : ℝ)|^4149 ≤ (5396674482843/12500000000000 : ℝ)^3125
        have hw : |(5311867161/10000000000 : ℝ)|=(5311867161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-423885223/2000000000 : ℝ)|^4149 ≤ (6373874264747/50000000000000 : ℝ)^3125
        have hw : |(-423885223/2000000000 : ℝ)|=(423885223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395560517/10000000000 : ℝ)|^4149 ≤ (5509856949783/12500000000000 : ℝ)^3125
        have hw : |(5395560517/10000000000 : ℝ)|=(5395560517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s5_6 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311867047/10000000000 : ℝ)*x 0 + (2697780383/5000000000 : ℝ)*x 1 + (-211942593/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311867047/10000000000 : ℝ)^4149 ≤ (5396674329071/12500000000000 : ℝ)^3125 := by
    have hnat : (5311867047 : ℕ)^4149*12500000000000^3125 ≤ 5396674329071^3125*10000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311867047 10000000000 5396674329071 12500000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697780383/5000000000 : ℝ)^4149 ≤ (44078858299027/100000000000000 : ℝ)^3125 := by
    have hnat : (2697780383 : ℕ)^4149*100000000000000^3125 ≤ 44078858299027^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697780383 5000000000 44078858299027 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211942593/1000000000 : ℝ)^4149 ≤ (6373873526077/50000000000000 : ℝ)^3125 := by
    have hnat : (211942593 : ℕ)^4149*50000000000000^3125 ≤ 6373873526077^3125*1000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211942593 1000000000 6373873526077 50000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311867047/10000000000 : ℝ), (2697780383/5000000000 : ℝ), (-211942593/1000000000 : ℝ)] ![(5396674329071/12500000000000 : ℝ), (44078858299027/100000000000000 : ℝ), (6373873526077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311867047/10000000000 : ℝ)|^4149 ≤ (5396674329071/12500000000000 : ℝ)^3125
        have hw : |(5311867047/10000000000 : ℝ)|=(5311867047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697780383/5000000000 : ℝ)|^4149 ≤ (44078858299027/100000000000000 : ℝ)^3125
        have hw : |(2697780383/5000000000 : ℝ)|=(2697780383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211942593/1000000000 : ℝ)|^4149 ≤ (6373873526077/50000000000000 : ℝ)^3125
        have hw : |(-211942593/1000000000 : ℝ)|=(211942593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1105_s5_7 (p : ℝ) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273113197/625000000 : ℝ)*x 0 + (2251153389/5000000000 : ℝ)*x 1 + (6786003/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273113197/625000000 : ℝ)^4149 ≤ (33315740906489/100000000000000 : ℝ)^3125 := by
    have hnat : (273113197 : ℕ)^4149*100000000000000^3125 ≤ 33315740906489^3125*625000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273113197 625000000 33315740906489 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251153389/5000000000 : ℝ)^4149 ≤ (34663522362323/100000000000000 : ℝ)^3125 := by
    have hnat : (2251153389 : ℕ)^4149*100000000000000^3125 ≤ 34663522362323^3125*5000000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251153389 5000000000 34663522362323 100000000000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6786003/16000000 : ℝ)^4149 ≤ (500324011233/1562500000000 : ℝ)^3125 := by
    have hnat : (6786003 : ℕ)^4149*1562500000000^3125 ≤ 500324011233^3125*16000000^4149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6786003 16000000 500324011233 1562500000000 4149 3125 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4149/1024 : ℝ)) 4149 3125 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273113197/625000000 : ℝ), (2251153389/5000000000 : ℝ), (6786003/16000000 : ℝ)] ![(33315740906489/100000000000000 : ℝ), (34663522362323/100000000000000 : ℝ), (500324011233/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273113197/625000000 : ℝ)|^4149 ≤ (33315740906489/100000000000000 : ℝ)^3125
        have hw : |(273113197/625000000 : ℝ)|=(273113197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251153389/5000000000 : ℝ)|^4149 ≤ (34663522362323/100000000000000 : ℝ)^3125
        have hw : |(2251153389/5000000000 : ℝ)|=(2251153389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6786003/16000000 : ℝ)|^4149 ≤ (500324011233/1562500000000 : ℝ)^3125
        have hw : |(6786003/16000000 : ℝ)|=(6786003/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1105_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (563/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11103/100000 : ℝ) ^ (8297/2048 : ℝ) ≤ (1697194227364649/12500000000000000000 : ℝ) := by
    have hpowers : (11103/100000 : ℝ)^8297 ≤ (1697194227364649/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11103 : ℕ)^8297*12500000000000000000^2048 ≤ 1697194227364649^2048*100000^8297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11103 100000 1697194227364649 12500000000000000000 8297 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11103/100000 : ℝ)) (X := (1697194227364649/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (8297/2048 : ℝ) ≤ (46484021552663/125000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^8297 ≤ (46484021552663/125000000000000000 : ℝ)^2048 := by
      have hnat : (7119 : ℕ)^8297*125000000000000000^2048 ≤ 46484021552663^2048*50000^8297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 46484021552663 125000000000000000 8297 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (46484021552663/125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251697194227364649/6250000000000000000 : ℝ) ≤ (10000670217840471/10000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (6251697194227364649/6250000000000000000 : ℝ)^2048 ≤ (10000670217840471/10000000000000000 : ℝ)^8297 := by
      have hnat : (6251697194227364649 : ℕ)^2048*10000000000000000^8297 ≤ 10000670217840471^8297*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251697194227364649 6250000000000000000 10000670217840471 10000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000670217840471/10000000000000000 : ℝ)) (X := (6251697194227364649/6250000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506345596382630949/12500000000000000000 : ℝ) ≤ (2000250563774139/2000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (12506345596382630949/12500000000000000000 : ℝ)^2048 ≤ (2000250563774139/2000000000000000 : ℝ)^8297 := by
      have hnat : (12506345596382630949 : ℕ)^2048*2000000000000000^8297 ≤ 2000250563774139^8297*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506345596382630949 12500000000000000000 2000250563774139 2000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000250563774139/2000000000000000 : ℝ)) (X := (12506345596382630949/12500000000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (62546484021552663/62500000000000000 : ℝ) ≤ (10001835419900919/10000000000000000 : ℝ) ^ (8297/2048 : ℝ) := by
    have hpowers : (62546484021552663/62500000000000000 : ℝ)^2048 ≤ (10001835419900919/10000000000000000 : ℝ)^8297 := by
      have hnat : (62546484021552663 : ℕ)^2048*10000000000000000^8297 ≤ 10001835419900919^8297*62500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62546484021552663 62500000000000000 10001835419900919 10000000000000000 2048 8297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001835419900919/10000000000000000 : ℝ)) (X := (62546484021552663/62500000000000000 : ℝ)) (by norm_num) 8297 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1697194227364649/12500000000000000000 : ℝ) ≤ ((10446387964817574147/10450000000000000000 : ℝ)+2*(12137521463/6531250000000 : ℝ)*(11103/100000 : ℝ))^(8297/2048 : ℝ) := by
    rw [show (10446387964817574147/10450000000000000000 : ℝ)+2*(12137521463/6531250000000 : ℝ)*(11103/100000 : ℝ)=(10000670217840471/10000000000000000 : ℝ) by norm_num, show 1+2*(1697194227364649/12500000000000000000 : ℝ)=(6251697194227364649/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46484021552663/125000000000000000 : ℝ)+(1697194227364649/12500000000000000000 : ℝ) ≤ ((10446387964817574147/10450000000000000000 : ℝ)+(12137521463/6531250000000 : ℝ)*((7119/50000 : ℝ)+(11103/100000 : ℝ)))^(8297/2048 : ℝ) := by
    rw [show (10446387964817574147/10450000000000000000 : ℝ)+(12137521463/6531250000000 : ℝ)*((7119/50000 : ℝ)+(11103/100000 : ℝ))=(2000250563774139/2000000000000000 : ℝ) by norm_num, show 1+(46484021552663/125000000000000000 : ℝ)+(1697194227364649/12500000000000000000 : ℝ)=(12506345596382630949/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46484021552663/125000000000000000 : ℝ) ≤ ((10446387964817574147/10450000000000000000 : ℝ)+2*(12137521463/6531250000000 : ℝ)*(7119/50000 : ℝ))^(8297/2048 : ℝ) := by
    rw [show (10446387964817574147/10450000000000000000 : ℝ)+2*(12137521463/6531250000000 : ℝ)*(7119/50000 : ℝ)=(10001835419900919/10000000000000000 : ℝ) by norm_num, show 1+2*(46484021552663/125000000000000000 : ℝ)=(62546484021552663/62500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10446387964817574147/10450000000000000000 : ℝ)*(X 1 0+X 2 0)+(12137521463/6531250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (10446387964817574147/10450000000000000000 : ℝ)) (alpha := (12137521463/6531250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10446387964817574147/10450000000000000000 : ℝ)*(X 0 1+X 2 1)+(12137521463/6531250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (10446387964817574147/10450000000000000000 : ℝ)) (alpha := (12137521463/6531250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10446387964817574147/10450000000000000000 : ℝ)*(X 0 2+X 1 2)+(12137521463/6531250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8297/2048 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (10446387964817574147/10450000000000000000 : ℝ)) (alpha := (12137521463/6531250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-17476101/80000000 : ℝ)*X 0 0+(5395906317/10000000000 : ℝ)*X 0 1+(1315759893/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672717643/5000000000 : ℝ)*X 1 0+(-450389411/2000000000 : ℝ)*X 1 1+(526303959/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345435319/10000000000 : ℝ)*X 2 0+(2631519793/5000000000 : ℝ)*X 2 1+(-2251947017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369800733/10000000000 : ℝ)*X 0 0+(2120284439/5000000000 : ℝ)*X 0 1+(225149341/500000000 : ℝ)*X 0 2+(4369800733/10000000000 : ℝ)*X 1 0+(2120284439/5000000000 : ℝ)*X 1 1+(225149341/500000000 : ℝ)*X 1 2+(4369800733/10000000000 : ℝ)*X 2 0+(2120284439/5000000000 : ℝ)*X 2 1+(225149341/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1092258797/5000000000 : ℝ)*X 0 0+(1052676869/2000000000 : ℝ)*X 0 1+(674445081/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311867161/10000000000 : ℝ)*X 1 0+(-423885223/2000000000 : ℝ)*X 1 1+(5395560517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311867047/10000000000 : ℝ)*X 2 0+(2697780383/5000000000 : ℝ)*X 2 1+(-211942593/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273113197/625000000 : ℝ)*X 0 0+(2251153389/5000000000 : ℝ)*X 0 1+(6786003/16000000 : ℝ)*X 0 2+(273113197/625000000 : ℝ)*X 1 0+(2251153389/5000000000 : ℝ)*X 1 1+(6786003/16000000 : ℝ)*X 1 2+(273113197/625000000 : ℝ)*X 2 0+(2251153389/5000000000 : ℝ)*X 2 1+(6786003/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1105_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81692506326100405554261387/26125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41738243/6250000000000 : ℝ)*(base19) + (709377071/100000000000000 : ℝ)*(base23) + (2618637/100000000000000 : ℝ)*(lower2) + (27331181/50000000000000 : ℝ)*(upper3) + (118711641/100000000000000 : ℝ)*(upper5) + (566855492767307/10000000000000 : ℝ)*(major0) + (566855492767307/10000000000000 : ℝ)*(major1) + (566855492767307/10000000000000 : ℝ)*(major2) + (1881588713909499/25000000000000 : ℝ)*(sp0) + (3763187478108921/50000000000000 : ℝ)*(sp1) + (7526374914652659/100000000000000 : ℝ)*(sp2) + (3810725060232181/100000000000000 : ℝ)*(sp3) + (10384195867/50000000000000 : ℝ)*(sp4) + (4533425677/50000000000000 : ℝ)*(sp7) + (238170882942721/6250000000000 : ℝ)*(f.failure) + (752637562402973/10000000000000 : ℝ)*(f.sum) + (11813721795187/1045000000000000000000000000 : ℝ)*base65 + (1483083143098387871/104500000000000000000000000000000 : ℝ)*base68 + (1626670241797387871/104500000000000000000000000000000 : ℝ)*base70 + (364101074797112129/104500000000000000000000000000000 : ℝ)*base71 + (867515344653/261250000000000000000000000 : ℝ)*base73 + (1275205750859387871/104500000000000000000000000000000 : ℝ)*base76 + (294906272943387871/104500000000000000000000000000000 : ℝ)*base78 + (2163642968252387871/104500000000000000000000000000000 : ℝ)*base80 + (909299383997/1045000000000000000000000000 : ℝ)*base81 + (10107347/625000000000000000000 : ℝ)*base89 + (10107347/625000000000000000000 : ℝ)*base91 + (10107347/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57589921170732852413217/5225000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119056423/25000000000000 : ℝ)*(base19) + (1037126819/100000000000000 : ℝ)*(base23) + (291751649/100000000000000 : ℝ)*(lower4) + (63861937/100000000000000 : ℝ)*(lower5) + (2849064339569007/50000000000000 : ℝ)*(major0) + (2849064339569007/50000000000000 : ℝ)*(major1) + (2849064339569007/50000000000000 : ℝ)*(major2) + (4533824803/50000000000000 : ℝ)*(sp1) + (2287842689/6250000000000 : ℝ)*(sp2) + (2552769563/100000000000000 : ℝ)*(sp3) + (30262566634181/400000000000 : ℝ)*(sp4) + (7565632114669951/100000000000000 : ℝ)*(sp5) + (472850250995963/6250000000000 : ℝ)*(sp6) + (3830612779561393/100000000000000 : ℝ)*(sp7) + (957653833082739/25000000000000 : ℝ)*(f.failure) + (30262566634181/400000000000 : ℝ)*(f.sum) + (38182978955837/5225000000000000000000000000 : ℝ)*base65 + (130499344176262029/522500000000000000000000000000000 : ℝ)*base67 + (4744190644206237971/522500000000000000000000000000000 : ℝ)*base70 + (660456712886262029/522500000000000000000000000000000 : ℝ)*base71 + (11701187437787/5225000000000000000000000000 : ℝ)*base73 + (3145295907636262029/522500000000000000000000000000000 : ℝ)*base75 + (3578820078726237971/522500000000000000000000000000000 : ℝ)*base78 + (827702612018737971/522500000000000000000000000000000 : ℝ)*base80 + (4448619322137/5225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1871127/2500000000000000000000 : ℝ)*base90 + (1871127/2500000000000000000000 : ℝ)*base92 + (1871127/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1105_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1105_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1105_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3323/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1105_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1105_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1105_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3323/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1105_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
