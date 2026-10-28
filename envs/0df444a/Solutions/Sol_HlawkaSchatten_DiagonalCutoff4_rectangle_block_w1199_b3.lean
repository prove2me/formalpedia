-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1199_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:57.266285+00:00
-- url     : https://prove2.me/submissions/aca9b8d0-c38c-44af-981c-81d5837ba93d

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
theorem support_rectangle_w1199_s9_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139925711/10000000000 : ℝ)*x 0 + (21567787/40000000 : ℝ)*x 1 + (1316664833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139925711/10000000000 : ℝ)^1049 ≤ (6504364193939/50000000000000 : ℝ)^793 := by
    have hnat : (2139925711 : ℕ)^1049*50000000000000^793 ≤ 6504364193939^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139925711 10000000000 6504364193939 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21567787/40000000 : ℝ)^1049 ≤ (22085968403723/50000000000000 : ℝ)^793 := by
    have hnat : (21567787 : ℕ)^1049*50000000000000^793 ≤ 22085968403723^793*40000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21567787 40000000 22085968403723 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316664833/2500000000 : ℝ)^1049 ≤ (21409667398987/50000000000000 : ℝ)^793 := by
    have hnat : (1316664833 : ℕ)^1049*50000000000000^793 ≤ 21409667398987^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316664833 2500000000 21409667398987 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139925711/10000000000 : ℝ), (21567787/40000000 : ℝ), (1316664833/2500000000 : ℝ)] ![(6504364193939/50000000000000 : ℝ), (22085968403723/50000000000000 : ℝ), (21409667398987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139925711/10000000000 : ℝ)|^1049 ≤ (6504364193939/50000000000000 : ℝ)^793
        have hw : |(-2139925711/10000000000 : ℝ)|=(2139925711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21567787/40000000 : ℝ)|^1049 ≤ (22085968403723/50000000000000 : ℝ)^793
        have hw : |(21567787/40000000 : ℝ)|=(21567787/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316664833/2500000000 : ℝ)|^1049 ≤ (21409667398987/50000000000000 : ℝ)^793
        have hw : |(1316664833/2500000000 : ℝ)|=(1316664833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s9_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1068901943/2000000000 : ℝ)*x 0 + (-550864793/2500000000 : ℝ)*x 1 + (1053331839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068901943/2000000000 : ℝ)^1049 ≤ (43658600138421/100000000000000 : ℝ)^793 := by
    have hnat : (1068901943 : ℕ)^1049*100000000000000^793 ≤ 43658600138421^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068901943 2000000000 43658600138421 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550864793/2500000000 : ℝ)^1049 ≤ (13522066530661/100000000000000 : ℝ)^793 := by
    have hnat : (550864793 : ℕ)^1049*100000000000000^793 ≤ 13522066530661^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550864793 2500000000 13522066530661 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053331839/2000000000 : ℝ)^1049 ≤ (856386666491/2000000000000 : ℝ)^793 := by
    have hnat : (1053331839 : ℕ)^1049*2000000000000^793 ≤ 856386666491^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053331839 2000000000 856386666491 2000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068901943/2000000000 : ℝ), (-550864793/2500000000 : ℝ), (1053331839/2000000000 : ℝ)] ![(43658600138421/100000000000000 : ℝ), (13522066530661/100000000000000 : ℝ), (856386666491/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068901943/2000000000 : ℝ)|^1049 ≤ (43658600138421/100000000000000 : ℝ)^793
        have hw : |(1068901943/2000000000 : ℝ)|=(1068901943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550864793/2500000000 : ℝ)|^1049 ≤ (13522066530661/100000000000000 : ℝ)^793
        have hw : |(-550864793/2500000000 : ℝ)|=(550864793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053331839/2000000000 : ℝ)|^1049 ≤ (856386666491/2000000000000 : ℝ)^793
        have hw : |(1053331839/2000000000 : ℝ)|=(1053331839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s9_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668063719/1250000000 : ℝ)*x 0 + (5266659229/10000000000 : ℝ)*x 1 + (-2203459077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668063719/1250000000 : ℝ)^1049 ≤ (21829300269121/50000000000000 : ℝ)^793 := by
    have hnat : (668063719 : ℕ)^1049*50000000000000^793 ≤ 21829300269121^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668063719 1250000000 21829300269121 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266659229/10000000000 : ℝ)^1049 ≤ (42819333690217/100000000000000 : ℝ)^793 := by
    have hnat : (5266659229 : ℕ)^1049*100000000000000^793 ≤ 42819333690217^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266659229 10000000000 42819333690217 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203459077/10000000000 : ℝ)^1049 ≤ (13522065759467/100000000000000 : ℝ)^793 := by
    have hnat : (2203459077 : ℕ)^1049*100000000000000^793 ≤ 13522065759467^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203459077 10000000000 13522065759467 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668063719/1250000000 : ℝ), (5266659229/10000000000 : ℝ), (-2203459077/10000000000 : ℝ)] ![(21829300269121/50000000000000 : ℝ), (42819333690217/100000000000000 : ℝ), (13522065759467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668063719/1250000000 : ℝ)|^1049 ≤ (21829300269121/50000000000000 : ℝ)^793
        have hw : |(668063719/1250000000 : ℝ)|=(668063719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266659229/10000000000 : ℝ)|^1049 ≤ (42819333690217/100000000000000 : ℝ)^793
        have hw : |(5266659229/10000000000 : ℝ)|=(5266659229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203459077/10000000000 : ℝ)|^1049 ≤ (13522065759467/100000000000000 : ℝ)^793
        have hw : |(-2203459077/10000000000 : ℝ)|=(2203459077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s9_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4356706763/10000000000 : ℝ)*x 0 + (529059203/1250000000 : ℝ)*x 1 + (4484519677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356706763/10000000000 : ℝ)^1049 ≤ (6663458783031/20000000000000 : ℝ)^793 := by
    have hnat : (4356706763 : ℕ)^1049*20000000000000^793 ≤ 6663458783031^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356706763 10000000000 6663458783031 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529059203/1250000000 : ℝ)^1049 ≤ (32066359588517/100000000000000 : ℝ)^793 := by
    have hnat : (529059203 : ℕ)^1049*100000000000000^793 ≤ 32066359588517^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529059203 1250000000 32066359588517 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484519677/10000000000 : ℝ)^1049 ≤ (1730817323997/5000000000000 : ℝ)^793 := by
    have hnat : (4484519677 : ℕ)^1049*5000000000000^793 ≤ 1730817323997^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484519677 10000000000 1730817323997 5000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356706763/10000000000 : ℝ), (529059203/1250000000 : ℝ), (4484519677/10000000000 : ℝ)] ![(6663458783031/20000000000000 : ℝ), (32066359588517/100000000000000 : ℝ), (1730817323997/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356706763/10000000000 : ℝ)|^1049 ≤ (6663458783031/20000000000000 : ℝ)^793
        have hw : |(4356706763/10000000000 : ℝ)|=(4356706763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529059203/1250000000 : ℝ)|^1049 ≤ (32066359588517/100000000000000 : ℝ)^793
        have hw : |(529059203/1250000000 : ℝ)|=(529059203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484519677/10000000000 : ℝ)|^1049 ≤ (1730817323997/5000000000000 : ℝ)^793
        have hw : |(4484519677/10000000000 : ℝ)|=(4484519677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s9_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069965223/5000000000 : ℝ)*x 0 + (1316743621/2500000000 : ℝ)*x 1 + (269581523/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069965223/5000000000 : ℝ)^1049 ≤ (2601753292903/20000000000000 : ℝ)^793 := by
    have hnat : (1069965223 : ℕ)^1049*20000000000000^793 ≤ 2601753292903^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069965223 5000000000 2601753292903 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316743621/2500000000 : ℝ)^1049 ≤ (2141136213187/5000000000000 : ℝ)^793 := by
    have hnat : (1316743621 : ℕ)^1049*5000000000000^793 ≤ 2141136213187^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316743621 2500000000 2141136213187 5000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269581523/500000000 : ℝ)^1049 ≤ (44168509251931/100000000000000 : ℝ)^793 := by
    have hnat : (269581523 : ℕ)^1049*100000000000000^793 ≤ 44168509251931^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269581523 500000000 44168509251931 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069965223/5000000000 : ℝ), (1316743621/2500000000 : ℝ), (269581523/500000000 : ℝ)] ![(2601753292903/20000000000000 : ℝ), (2141136213187/5000000000000 : ℝ), (44168509251931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069965223/5000000000 : ℝ)|^1049 ≤ (2601753292903/20000000000000 : ℝ)^793
        have hw : |(-1069965223/5000000000 : ℝ)|=(1069965223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316743621/2500000000 : ℝ)|^1049 ≤ (2141136213187/5000000000000 : ℝ)^793
        have hw : |(1316743621/2500000000 : ℝ)|=(1316743621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269581523/500000000 : ℝ)|^1049 ≤ (44168509251931/100000000000000 : ℝ)^793
        have hw : |(269581523/500000000 : ℝ)|=(269581523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s9_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328159129/2500000000 : ℝ)*x 0 + (-1039243987/5000000000 : ℝ)*x 1 + (269581523/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328159129/2500000000 : ℝ)^1049 ≤ (43314510920301/100000000000000 : ℝ)^793 := by
    have hnat : (1328159129 : ℕ)^1049*100000000000000^793 ≤ 43314510920301^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328159129 2500000000 43314510920301 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039243987/5000000000 : ℝ)^1049 ≤ (12516979803763/100000000000000 : ℝ)^793 := by
    have hnat : (1039243987 : ℕ)^1049*100000000000000^793 ≤ 12516979803763^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039243987 5000000000 12516979803763 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269581523/500000000 : ℝ)^1049 ≤ (44168509251931/100000000000000 : ℝ)^793 := by
    have hnat : (269581523 : ℕ)^1049*100000000000000^793 ≤ 44168509251931^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269581523 500000000 44168509251931 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328159129/2500000000 : ℝ), (-1039243987/5000000000 : ℝ), (269581523/500000000 : ℝ)] ![(43314510920301/100000000000000 : ℝ), (12516979803763/100000000000000 : ℝ), (44168509251931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328159129/2500000000 : ℝ)|^1049 ≤ (43314510920301/100000000000000 : ℝ)^793
        have hw : |(1328159129/2500000000 : ℝ)|=(1328159129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039243987/5000000000 : ℝ)|^1049 ≤ (12516979803763/100000000000000 : ℝ)^793
        have hw : |(-1039243987/5000000000 : ℝ)|=(1039243987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269581523/500000000 : ℝ)|^1049 ≤ (44168509251931/100000000000000 : ℝ)^793
        have hw : |(269581523/500000000 : ℝ)|=(269581523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s9_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2178358173/5000000000 : ℝ)*x 0 + (280242847/625000000 : ℝ)*x 1 + (4233109999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178358173/5000000000 : ℝ)^1049 ≤ (6663478171581/20000000000000 : ℝ)^793 := by
    have hnat : (2178358173 : ℕ)^1049*20000000000000^793 ≤ 6663478171581^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178358173 5000000000 6663478171581 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280242847/625000000 : ℝ)^1049 ≤ (34609871587497/100000000000000 : ℝ)^793 := by
    have hnat : (280242847 : ℕ)^1049*100000000000000^793 ≤ 34609871587497^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280242847 625000000 34609871587497 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233109999/10000000000 : ℝ)^1049 ≤ (6414547508403/20000000000000 : ℝ)^793 := by
    have hnat : (4233109999 : ℕ)^1049*20000000000000^793 ≤ 6414547508403^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233109999 10000000000 6414547508403 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178358173/5000000000 : ℝ), (280242847/625000000 : ℝ), (4233109999/10000000000 : ℝ)] ![(6663478171581/20000000000000 : ℝ), (34609871587497/100000000000000 : ℝ), (6414547508403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178358173/5000000000 : ℝ)|^1049 ≤ (6663478171581/20000000000000 : ℝ)^793
        have hw : |(2178358173/5000000000 : ℝ)|=(2178358173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280242847/625000000 : ℝ)|^1049 ≤ (34609871587497/100000000000000 : ℝ)^793
        have hw : |(280242847/625000000 : ℝ)|=(280242847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233109999/10000000000 : ℝ)|^1049 ≤ (6414547508403/20000000000000 : ℝ)^793
        have hw : |(4233109999/10000000000 : ℝ)|=(4233109999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11427/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5713/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5713/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5713/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5713/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5713/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5713/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5713/50000 : ℝ) ^ (8391/2048 : ℝ) ≤ (2760987049331673/20000000000000000000 : ℝ) := by
    have hpowers : (5713/50000 : ℝ)^8391 ≤ (2760987049331673/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5713 : ℕ)^8391*20000000000000000000^2048 ≤ 2760987049331673^2048*50000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5713 50000 2760987049331673 20000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5713/50000 : ℝ)) (X := (2760987049331673/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14081/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (32494393871606633/100000000000000000000 : ℝ) := by
    have hpowers : (14081/100000 : ℝ)^8391 ≤ (32494393871606633/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14081 : ℕ)^8391*100000000000000000000^2048 ≤ 32494393871606633^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14081 100000 32494393871606633 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14081/100000 : ℝ)) (X := (32494393871606633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002760987049331673/10000000000000000000 : ℝ) ≤ (1250084225829669/1250000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (10002760987049331673/10000000000000000000 : ℝ)^2048 ≤ (1250084225829669/1250000000000000 : ℝ)^8391 := by
      have hnat : (10002760987049331673 : ℕ)^2048*1250000000000000^8391 ≤ 1250084225829669^8391*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002760987049331673 10000000000000000000 1250084225829669 1250000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250084225829669/1250000000000000 : ℝ)) (X := (10002760987049331673/10000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023149664559132499/50000000000000000000 : ℝ) ≤ (1000112983479111/1000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50023149664559132499/50000000000000000000 : ℝ)^2048 ≤ (1000112983479111/1000000000000000 : ℝ)^8391 := by
      have hnat : (50023149664559132499 : ℕ)^2048*1000000000000000^8391 ≤ 1000112983479111^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023149664559132499 50000000000000000000 1000112983479111 1000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000112983479111/1000000000000000 : ℝ)) (X := (50023149664559132499/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032494393871606633/50000000000000000000 : ℝ) ≤ (2500396465736217/2500000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50032494393871606633/50000000000000000000 : ℝ)^2048 ≤ (2500396465736217/2500000000000000 : ℝ)^8391 := by
      have hnat : (50032494393871606633 : ℕ)^2048*2500000000000000^8391 ≤ 2500396465736217^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032494393871606633 50000000000000000000 2500396465736217 2500000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500396465736217/2500000000000000 : ℝ)) (X := (50032494393871606633/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2760987049331673/20000000000000000000 : ℝ) ≤ ((92157527087682263/92187500000000000 : ℝ)+2*(25334897431/14750000000000 : ℝ)*(5713/50000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (92157527087682263/92187500000000000 : ℝ)+2*(25334897431/14750000000000 : ℝ)*(5713/50000 : ℝ)=(1250084225829669/1250000000000000 : ℝ) by norm_num, show 1+2*(2760987049331673/20000000000000000000 : ℝ)=(10002760987049331673/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32494393871606633/100000000000000000000 : ℝ)+(2760987049331673/20000000000000000000 : ℝ) ≤ ((92157527087682263/92187500000000000 : ℝ)+(25334897431/14750000000000 : ℝ)*((14081/100000 : ℝ)+(5713/50000 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (92157527087682263/92187500000000000 : ℝ)+(25334897431/14750000000000 : ℝ)*((14081/100000 : ℝ)+(5713/50000 : ℝ))=(1000112983479111/1000000000000000 : ℝ) by norm_num, show 1+(32494393871606633/100000000000000000000 : ℝ)+(2760987049331673/20000000000000000000 : ℝ)=(50023149664559132499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32494393871606633/100000000000000000000 : ℝ) ≤ ((92157527087682263/92187500000000000 : ℝ)+2*(25334897431/14750000000000 : ℝ)*(14081/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (92157527087682263/92187500000000000 : ℝ)+2*(25334897431/14750000000000 : ℝ)*(14081/100000 : ℝ)=(2500396465736217/2500000000000000 : ℝ) by norm_num, show 1+2*(32494393871606633/100000000000000000000 : ℝ)=(50032494393871606633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92157527087682263/92187500000000000 : ℝ)*(X 1 0+X 2 0)+(25334897431/14750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (92157527087682263/92187500000000000 : ℝ)) (alpha := (25334897431/14750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92157527087682263/92187500000000000 : ℝ)*(X 0 1+X 2 1)+(25334897431/14750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (92157527087682263/92187500000000000 : ℝ)) (alpha := (25334897431/14750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92157527087682263/92187500000000000 : ℝ)*(X 0 2+X 1 2)+(25334897431/14750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (92157527087682263/92187500000000000 : ℝ)) (alpha := (25334897431/14750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139925711/10000000000 : ℝ)*X 0 0+(21567787/40000000 : ℝ)*X 0 1+(1316664833/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068901943/2000000000 : ℝ)*X 1 0+(-550864793/2500000000 : ℝ)*X 1 1+(1053331839/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668063719/1250000000 : ℝ)*X 2 0+(5266659229/10000000000 : ℝ)*X 2 1+(-2203459077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356706763/10000000000 : ℝ)*X 0 0+(529059203/1250000000 : ℝ)*X 0 1+(4484519677/10000000000 : ℝ)*X 0 2+(4356706763/10000000000 : ℝ)*X 1 0+(529059203/1250000000 : ℝ)*X 1 1+(4484519677/10000000000 : ℝ)*X 1 2+(4356706763/10000000000 : ℝ)*X 2 0+(529059203/1250000000 : ℝ)*X 2 1+(4484519677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1069965223/5000000000 : ℝ)*X 0 0+(1316743621/2500000000 : ℝ)*X 0 1+(269581523/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328159129/2500000000 : ℝ)*X 1 0+(-1039243987/5000000000 : ℝ)*X 1 1+(269581523/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2178358173/5000000000 : ℝ)*X 0 0+(280242847/625000000 : ℝ)*X 0 1+(4233109999/10000000000 : ℝ)*X 0 2+(2178358173/5000000000 : ℝ)*X 1 0+(280242847/625000000 : ℝ)*X 1 1+(4233109999/10000000000 : ℝ)*X 1 2+(2178358173/5000000000 : ℝ)*X 2 0+(280242847/625000000 : ℝ)*X 2 1+(4233109999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3839327283951352102834779/2304687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (35725897/6250000000000 : ℝ)*(base19) + (630949107/100000000000000 : ℝ)*(base23) + (2618773/25000000000000 : ℝ)*(upper4) + (13490887/25000000000000 : ℝ)*(upper5) + (5974612112778697/100000000000000 : ℝ)*(major0) + (5974612112778697/100000000000000 : ℝ)*(major1) + (5974612112778697/100000000000000 : ℝ)*(major2) + (7981660372569593/100000000000000 : ℝ)*(sp0) + (3990836350592641/50000000000000 : ℝ)*(sp1) + (7981676612085049/100000000000000 : ℝ)*(sp2) + (495942272981259/12500000000000 : ℝ)*(sp3) + (16870464563/100000000000000 : ℝ)*(sp4) + (3970234523/100000000000000 : ℝ)*(sp5) + (273223247/3125000000000 : ℝ)*(sp6) + (495943365874247/12500000000000 : ℝ)*(f.failure) + (1995419310758539/25000000000000 : ℝ)*(f.sum) + (510547181289/1475000000000000000000000000 : ℝ)*base65 + (204980208379742439/9218750000000000000000000000000 : ℝ)*base68 + (74673956280054939/9218750000000000000000000000000 : ℝ)*base70 + (87256111407757561/9218750000000000000000000000000 : ℝ)*base71 + (2631108078609/368750000000000000000000000 : ℝ)*base74 + (115052613330992439/9218750000000000000000000000000 : ℝ)*base76 + (3052988537554939/9218750000000000000000000000000 : ℝ)*base78 + (38612501813851311/9218750000000000000000000000000 : ℝ)*base79 + (6544262869011/1475000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (590427/78125000000000000000 : ℝ)*base89 + (590427/78125000000000000000 : ℝ)*base91 + (590427/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1199_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1199_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1199_box_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014876867/10000000000 : ℝ)*x 0 + (5375484129/10000000000 : ℝ)*x 1 + (5375483967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014876867/10000000000 : ℝ)^1049 ≤ (1501594768689/12500000000000 : ℝ)^793 := by
    have hnat : (2014876867 : ℕ)^1049*12500000000000^793 ≤ 1501594768689^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014876867 10000000000 1501594768689 12500000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375484129/10000000000 : ℝ)^1049 ≤ (43993621799139/100000000000000 : ℝ)^793 := by
    have hnat : (5375484129 : ℕ)^1049*100000000000000^793 ≤ 43993621799139^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375484129 10000000000 43993621799139 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375483967/10000000000 : ℝ)^1049 ≤ (43993620045301/100000000000000 : ℝ)^793 := by
    have hnat : (5375483967 : ℕ)^1049*100000000000000^793 ≤ 43993620045301^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375483967 10000000000 43993620045301 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014876867/10000000000 : ℝ), (5375484129/10000000000 : ℝ), (5375483967/10000000000 : ℝ)] ![(1501594768689/12500000000000 : ℝ), (43993621799139/100000000000000 : ℝ), (43993620045301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014876867/10000000000 : ℝ)|^1049 ≤ (1501594768689/12500000000000 : ℝ)^793
        have hw : |(-2014876867/10000000000 : ℝ)|=(2014876867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375484129/10000000000 : ℝ)|^1049 ≤ (43993621799139/100000000000000 : ℝ)^793
        have hw : |(5375484129/10000000000 : ℝ)|=(5375484129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375483967/10000000000 : ℝ)|^1049 ≤ (43993620045301/100000000000000 : ℝ)^793
        have hw : |(5375483967/10000000000 : ℝ)|=(5375483967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1324119141/2500000000 : ℝ)*x 0 + (-530540413/2500000000 : ℝ)*x 1 + (5375484027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324119141/2500000000 : ℝ)^1049 ≤ (43140309276451/100000000000000 : ℝ)^793 := by
    have hnat : (1324119141 : ℕ)^1049*100000000000000^793 ≤ 43140309276451^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324119141 2500000000 43140309276451 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530540413/2500000000 : ℝ)^1049 ≤ (12866070020537/100000000000000 : ℝ)^793 := by
    have hnat : (530540413 : ℕ)^1049*100000000000000^793 ≤ 12866070020537^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530540413 2500000000 12866070020537 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375484027/10000000000 : ℝ)^1049 ≤ (43993620694871/100000000000000 : ℝ)^793 := by
    have hnat : (5375484027 : ℕ)^1049*100000000000000^793 ≤ 43993620694871^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375484027 10000000000 43993620694871 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324119141/2500000000 : ℝ), (-530540413/2500000000 : ℝ), (5375484027/10000000000 : ℝ)] ![(43140309276451/100000000000000 : ℝ), (12866070020537/100000000000000 : ℝ), (43993620694871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324119141/2500000000 : ℝ)|^1049 ≤ (43140309276451/100000000000000 : ℝ)^793
        have hw : |(1324119141/2500000000 : ℝ)|=(1324119141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530540413/2500000000 : ℝ)|^1049 ≤ (12866070020537/100000000000000 : ℝ)^793
        have hw : |(-530540413/2500000000 : ℝ)|=(530540413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375484027/10000000000 : ℝ)|^1049 ≤ (43993620694871/100000000000000 : ℝ)^793
        have hw : |(5375484027/10000000000 : ℝ)|=(5375484027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21185907/40000000 : ℝ)*x 0 + (53754839/100000000 : ℝ)*x 1 + (-2122161573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21185907/40000000 : ℝ)^1049 ≤ (21570155640257/50000000000000 : ℝ)^793 := by
    have hnat : (21185907 : ℕ)^1049*50000000000000^793 ≤ 21570155640257^793*40000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21185907 40000000 21570155640257 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53754839/100000000 : ℝ)^1049 ≤ (10998404829987/25000000000000 : ℝ)^793 := by
    have hnat : (53754839 : ℕ)^1049*25000000000000^793 ≤ 10998404829987^793*100000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53754839 100000000 10998404829987 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122161573/10000000000 : ℝ)^1049 ≤ (3216517346741/25000000000000 : ℝ)^793 := by
    have hnat : (2122161573 : ℕ)^1049*25000000000000^793 ≤ 3216517346741^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122161573 10000000000 3216517346741 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21185907/40000000 : ℝ), (53754839/100000000 : ℝ), (-2122161573/10000000000 : ℝ)] ![(21570155640257/50000000000000 : ℝ), (10998404829987/25000000000000 : ℝ), (3216517346741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21185907/40000000 : ℝ)|^1049 ≤ (21570155640257/50000000000000 : ℝ)^793
        have hw : |(21185907/40000000 : ℝ)|=(21185907/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53754839/100000000 : ℝ)|^1049 ≤ (10998404829987/25000000000000 : ℝ)^793
        have hw : |(53754839/100000000 : ℝ)|=(53754839/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122161573/10000000000 : ℝ)|^1049 ≤ (3216517346741/25000000000000 : ℝ)^793
        have hw : |(-2122161573/10000000000 : ℝ)|=(2122161573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (446365857/1000000000 : ℝ)*x 0 + (4305300113/10000000000 : ℝ)*x 1 + (538162549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446365857/1000000000 : ℝ)^1049 ≤ (34403494160451/100000000000000 : ℝ)^793 := by
    have hnat : (446365857 : ℕ)^1049*100000000000000^793 ≤ 34403494160451^793*1000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446365857 1000000000 34403494160451 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4305300113/10000000000 : ℝ)^1049 ≤ (32798251508817/100000000000000 : ℝ)^793 := by
    have hnat : (4305300113 : ℕ)^1049*100000000000000^793 ≤ 32798251508817^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305300113 10000000000 32798251508817 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538162549/1250000000 : ℝ)^1049 ≤ (16399127160209/50000000000000 : ℝ)^793 := by
    have hnat : (538162549 : ℕ)^1049*50000000000000^793 ≤ 16399127160209^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538162549 1250000000 16399127160209 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(446365857/1000000000 : ℝ), (4305300113/10000000000 : ℝ), (538162549/1250000000 : ℝ)] ![(34403494160451/100000000000000 : ℝ), (32798251508817/100000000000000 : ℝ), (16399127160209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(446365857/1000000000 : ℝ)|^1049 ≤ (34403494160451/100000000000000 : ℝ)^793
        have hw : |(446365857/1000000000 : ℝ)|=(446365857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4305300113/10000000000 : ℝ)|^1049 ≤ (32798251508817/100000000000000 : ℝ)^793
        have hw : |(4305300113/10000000000 : ℝ)|=(4305300113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538162549/1250000000 : ℝ)|^1049 ≤ (16399127160209/50000000000000 : ℝ)^793
        have hw : |(538162549/1250000000 : ℝ)|=(538162549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1133175041/5000000000 : ℝ)*x 0 + (5281826169/10000000000 : ℝ)*x 1 + (330114141/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1133175041/5000000000 : ℝ)^1049 ≤ (2806988362009/20000000000000 : ℝ)^793 := by
    have hnat : (1133175041 : ℕ)^1049*20000000000000^793 ≤ 2806988362009^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133175041 5000000000 2806988362009 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281826169/10000000000 : ℝ)^1049 ≤ (8596505723367/20000000000000 : ℝ)^793 := by
    have hnat : (5281826169 : ℕ)^1049*20000000000000^793 ≤ 8596505723367^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281826169 10000000000 8596505723367 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330114141/625000000 : ℝ)^1049 ≤ (42982529553381/100000000000000 : ℝ)^793 := by
    have hnat : (330114141 : ℕ)^1049*100000000000000^793 ≤ 42982529553381^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330114141 625000000 42982529553381 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1133175041/5000000000 : ℝ), (5281826169/10000000000 : ℝ), (330114141/625000000 : ℝ)] ![(2806988362009/20000000000000 : ℝ), (8596505723367/20000000000000 : ℝ), (42982529553381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1133175041/5000000000 : ℝ)|^1049 ≤ (2806988362009/20000000000000 : ℝ)^793
        have hw : |(-1133175041/5000000000 : ℝ)|=(1133175041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281826169/10000000000 : ℝ)|^1049 ≤ (8596505723367/20000000000000 : ℝ)^793
        have hw : |(5281826169/10000000000 : ℝ)|=(5281826169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330114141/625000000 : ℝ)|^1049 ≤ (42982529553381/100000000000000 : ℝ)^793
        have hw : |(330114141/625000000 : ℝ)|=(330114141/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5362561193/10000000000 : ℝ)*x 0 + (-1079584733/5000000000 : ℝ)*x 1 + (1056365221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362561193/10000000000 : ℝ)^1049 ≤ (43853770347711/100000000000000 : ℝ)^793 := by
    have hnat : (5362561193 : ℕ)^1049*100000000000000^793 ≤ 43853770347711^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362561193 10000000000 43853770347711 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079584733/5000000000 : ℝ)^1049 ≤ (6581850853287/50000000000000 : ℝ)^793 := by
    have hnat : (1079584733 : ℕ)^1049*50000000000000^793 ≤ 6581850853287^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079584733 5000000000 6581850853287 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056365221/2000000000 : ℝ)^1049 ≤ (42982527927881/100000000000000 : ℝ)^793 := by
    have hnat : (1056365221 : ℕ)^1049*100000000000000^793 ≤ 42982527927881^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056365221 2000000000 42982527927881 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362561193/10000000000 : ℝ), (-1079584733/5000000000 : ℝ), (1056365221/2000000000 : ℝ)] ![(43853770347711/100000000000000 : ℝ), (6581850853287/50000000000000 : ℝ), (42982527927881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362561193/10000000000 : ℝ)|^1049 ≤ (43853770347711/100000000000000 : ℝ)^793
        have hw : |(5362561193/10000000000 : ℝ)|=(5362561193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1079584733/5000000000 : ℝ)|^1049 ≤ (6581850853287/50000000000000 : ℝ)^793
        have hw : |(-1079584733/5000000000 : ℝ)|=(1079584733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056365221/2000000000 : ℝ)|^1049 ≤ (42982527927881/100000000000000 : ℝ)^793
        have hw : |(1056365221/2000000000 : ℝ)|=(1056365221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5362561743/10000000000 : ℝ)*x 0 + (2640913099/5000000000 : ℝ)*x 1 + (-431833721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362561743/10000000000 : ℝ)^1049 ≤ (21926888148737/50000000000000 : ℝ)^793 := by
    have hnat : (5362561743 : ℕ)^1049*50000000000000^793 ≤ 21926888148737^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362561743 10000000000 21926888148737 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640913099/5000000000 : ℝ)^1049 ≤ (42982528929017/100000000000000 : ℝ)^793 := by
    have hnat : (2640913099 : ℕ)^1049*100000000000000^793 ≤ 42982528929017^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640913099 5000000000 42982528929017 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431833721/2000000000 : ℝ)^1049 ≤ (6581847381391/50000000000000 : ℝ)^793 := by
    have hnat : (431833721 : ℕ)^1049*50000000000000^793 ≤ 6581847381391^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431833721 2000000000 6581847381391 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362561743/10000000000 : ℝ), (2640913099/5000000000 : ℝ), (-431833721/2000000000 : ℝ)] ![(21926888148737/50000000000000 : ℝ), (42982528929017/100000000000000 : ℝ), (6581847381391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362561743/10000000000 : ℝ)|^1049 ≤ (21926888148737/50000000000000 : ℝ)^793
        have hw : |(5362561743/10000000000 : ℝ)|=(5362561743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640913099/5000000000 : ℝ)|^1049 ≤ (42982528929017/100000000000000 : ℝ)^793
        have hw : |(2640913099/5000000000 : ℝ)|=(2640913099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-431833721/2000000000 : ℝ)|^1049 ≤ (6581847381391/50000000000000 : ℝ)^793
        have hw : |(-431833721/2000000000 : ℝ)|=(431833721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_7 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265585587/625000000 : ℝ)*x 0 + (2206212573/5000000000 : ℝ)*x 1 + (1103105929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265585587/625000000 : ℝ)^1049 ≤ (8058949817999/25000000000000 : ℝ)^793 := by
    have hnat : (265585587 : ℕ)^1049*25000000000000^793 ≤ 8058949817999^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265585587 625000000 8058949817999 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206212573/5000000000 : ℝ)^1049 ≤ (8470526904639/25000000000000 : ℝ)^793 := by
    have hnat : (2206212573 : ℕ)^1049*25000000000000^793 ≤ 8470526904639^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206212573 5000000000 8470526904639 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103105929/2500000000 : ℝ)^1049 ≤ (16941046546523/50000000000000 : ℝ)^793 := by
    have hnat : (1103105929 : ℕ)^1049*50000000000000^793 ≤ 16941046546523^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103105929 2500000000 16941046546523 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265585587/625000000 : ℝ), (2206212573/5000000000 : ℝ), (1103105929/2500000000 : ℝ)] ![(8058949817999/25000000000000 : ℝ), (8470526904639/25000000000000 : ℝ), (16941046546523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265585587/625000000 : ℝ)|^1049 ≤ (8058949817999/25000000000000 : ℝ)^793
        have hw : |(265585587/625000000 : ℝ)|=(265585587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2206212573/5000000000 : ℝ)|^1049 ≤ (8470526904639/25000000000000 : ℝ)^793
        have hw : |(2206212573/5000000000 : ℝ)|=(2206212573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103105929/2500000000 : ℝ)|^1049 ≤ (16941046546523/50000000000000 : ℝ)^793
        have hw : |(1103105929/2500000000 : ℝ)|=(1103105929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_8 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106849993/5000000000 : ℝ)*x 0 + (16306319/31250000 : ℝ)*x 1 + (5385095979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106849993/5000000000 : ℝ)^1049 ≤ (13605262095819/100000000000000 : ℝ)^793 := by
    have hnat : (1106849993 : ℕ)^1049*100000000000000^793 ≤ 13605262095819^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106849993 5000000000 13605262095819 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16306319/31250000 : ℝ)^1049 ≤ (42297026644019/100000000000000 : ℝ)^793 := by
    have hnat : (16306319 : ℕ)^1049*100000000000000^793 ≤ 42297026644019^793*31250000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16306319 31250000 42297026644019 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385095979/10000000000 : ℝ)^1049 ≤ (44097711244877/100000000000000 : ℝ)^793 := by
    have hnat : (5385095979 : ℕ)^1049*100000000000000^793 ≤ 44097711244877^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385095979 10000000000 44097711244877 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106849993/5000000000 : ℝ), (16306319/31250000 : ℝ), (5385095979/10000000000 : ℝ)] ![(13605262095819/100000000000000 : ℝ), (42297026644019/100000000000000 : ℝ), (44097711244877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106849993/5000000000 : ℝ)|^1049 ≤ (13605262095819/100000000000000 : ℝ)^793
        have hw : |(-1106849993/5000000000 : ℝ)|=(1106849993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16306319/31250000 : ℝ)|^1049 ≤ (42297026644019/100000000000000 : ℝ)^793
        have hw : |(16306319/31250000 : ℝ)|=(16306319/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385095979/10000000000 : ℝ)|^1049 ≤ (44097711244877/100000000000000 : ℝ)^793
        have hw : |(5385095979/10000000000 : ℝ)|=(5385095979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_9 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2644845683/5000000000 : ℝ)*x 0 + (-2118295343/10000000000 : ℝ)*x 1 + (269254799/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644845683/5000000000 : ℝ)^1049 ≤ (43067217050827/100000000000000 : ℝ)^793 := by
    have hnat : (2644845683 : ℕ)^1049*100000000000000^793 ≤ 43067217050827^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644845683 5000000000 43067217050827 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118295343/10000000000 : ℝ)^1049 ≤ (12835071674367/100000000000000 : ℝ)^793 := by
    have hnat : (2118295343 : ℕ)^1049*100000000000000^793 ≤ 12835071674367^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118295343 10000000000 12835071674367 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269254799/500000000 : ℝ)^1049 ≤ (44097711255709/100000000000000 : ℝ)^793 := by
    have hnat : (269254799 : ℕ)^1049*100000000000000^793 ≤ 44097711255709^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269254799 500000000 44097711255709 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644845683/5000000000 : ℝ), (-2118295343/10000000000 : ℝ), (269254799/500000000 : ℝ)] ![(43067217050827/100000000000000 : ℝ), (12835071674367/100000000000000 : ℝ), (44097711255709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644845683/5000000000 : ℝ)|^1049 ≤ (43067217050827/100000000000000 : ℝ)^793
        have hw : |(2644845683/5000000000 : ℝ)|=(2644845683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2118295343/10000000000 : ℝ)|^1049 ≤ (12835071674367/100000000000000 : ℝ)^793
        have hw : |(-2118295343/10000000000 : ℝ)|=(2118295343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269254799/500000000 : ℝ)|^1049 ≤ (44097711255709/100000000000000 : ℝ)^793
        have hw : |(269254799/500000000 : ℝ)|=(269254799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_10 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5289691349/10000000000 : ℝ)*x 0 + (5385095981/10000000000 : ℝ)*x 1 + (-423659073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289691349/10000000000 : ℝ)^1049 ≤ (5383402108467/12500000000000 : ℝ)^793 := by
    have hnat : (5289691349 : ℕ)^1049*12500000000000^793 ≤ 5383402108467^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289691349 10000000000 5383402108467 12500000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385095981/10000000000 : ℝ)^1049 ≤ (22048855633271/50000000000000 : ℝ)^793 := by
    have hnat : (5385095981 : ℕ)^1049*50000000000000^793 ≤ 22048855633271^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385095981 10000000000 22048855633271 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423659073/2000000000 : ℝ)^1049 ≤ (6417535925351/50000000000000 : ℝ)^793 := by
    have hnat : (423659073 : ℕ)^1049*50000000000000^793 ≤ 6417535925351^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423659073 2000000000 6417535925351 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289691349/10000000000 : ℝ), (5385095981/10000000000 : ℝ), (-423659073/2000000000 : ℝ)] ![(5383402108467/12500000000000 : ℝ), (22048855633271/50000000000000 : ℝ), (6417535925351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289691349/10000000000 : ℝ)|^1049 ≤ (5383402108467/12500000000000 : ℝ)^793
        have hw : |(5289691349/10000000000 : ℝ)|=(5289691349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385095981/10000000000 : ℝ)|^1049 ≤ (22048855633271/50000000000000 : ℝ)^793
        have hw : |(5385095981/10000000000 : ℝ)|=(5385095981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423659073/2000000000 : ℝ)|^1049 ≤ (6417535925351/50000000000000 : ℝ)^793
        have hw : |(-423659073/2000000000 : ℝ)|=(423659073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_11 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4485378203/10000000000 : ℝ)*x 0 + (1073574981/2500000000 : ℝ)*x 1 + (4294299873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4485378203/10000000000 : ℝ)^1049 ≤ (34625113146077/100000000000000 : ℝ)^793 := by
    have hnat : (4485378203 : ℕ)^1049*100000000000000^793 ≤ 34625113146077^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485378203 10000000000 34625113146077 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073574981/2500000000 : ℝ)^1049 ≤ (32687443676337/100000000000000 : ℝ)^793 := by
    have hnat : (1073574981 : ℕ)^1049*100000000000000^793 ≤ 32687443676337^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073574981 2500000000 32687443676337 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4294299873/10000000000 : ℝ)^1049 ≤ (32687443162813/100000000000000 : ℝ)^793 := by
    have hnat : (4294299873 : ℕ)^1049*100000000000000^793 ≤ 32687443162813^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294299873 10000000000 32687443162813 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4485378203/10000000000 : ℝ), (1073574981/2500000000 : ℝ), (4294299873/10000000000 : ℝ)] ![(34625113146077/100000000000000 : ℝ), (32687443676337/100000000000000 : ℝ), (32687443162813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4485378203/10000000000 : ℝ)|^1049 ≤ (34625113146077/100000000000000 : ℝ)^793
        have hw : |(4485378203/10000000000 : ℝ)|=(4485378203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1073574981/2500000000 : ℝ)|^1049 ≤ (32687443676337/100000000000000 : ℝ)^793
        have hw : |(1073574981/2500000000 : ℝ)|=(1073574981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4294299873/10000000000 : ℝ)|^1049 ≤ (32687443162813/100000000000000 : ℝ)^793
        have hw : |(4294299873/10000000000 : ℝ)|=(4294299873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_12 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033905883/5000000000 : ℝ)*x 0 + (5438050469/10000000000 : ℝ)*x 1 + (5273763373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033905883/5000000000 : ℝ)^1049 ≤ (12432000978811/100000000000000 : ℝ)^793 := by
    have hnat : (1033905883 : ℕ)^1049*100000000000000^793 ≤ 12432000978811^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033905883 5000000000 12432000978811 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438050469/10000000000 : ℝ)^1049 ≤ (1396007631839/3125000000000 : ℝ)^793 := by
    have hnat : (5438050469 : ℕ)^1049*3125000000000^793 ≤ 1396007631839^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438050469 10000000000 1396007631839 3125000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273763373/10000000000 : ℝ)^1049 ≤ (5361969348273/12500000000000 : ℝ)^793 := by
    have hnat : (5273763373 : ℕ)^1049*12500000000000^793 ≤ 5361969348273^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273763373 10000000000 5361969348273 12500000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033905883/5000000000 : ℝ), (5438050469/10000000000 : ℝ), (5273763373/10000000000 : ℝ)] ![(12432000978811/100000000000000 : ℝ), (1396007631839/3125000000000 : ℝ), (5361969348273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033905883/5000000000 : ℝ)|^1049 ≤ (12432000978811/100000000000000 : ℝ)^793
        have hw : |(-1033905883/5000000000 : ℝ)|=(1033905883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438050469/10000000000 : ℝ)|^1049 ≤ (1396007631839/3125000000000 : ℝ)^793
        have hw : |(5438050469/10000000000 : ℝ)|=(5438050469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273763373/10000000000 : ℝ)|^1049 ≤ (5361969348273/12500000000000 : ℝ)^793
        have hw : |(5273763373/10000000000 : ℝ)|=(5273763373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_13 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (671031101/1250000000 : ℝ)*x 0 + (-2162298009/10000000000 : ℝ)*x 1 + (1318440807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671031101/1250000000 : ℝ)^1049 ≤ (10978827020217/25000000000000 : ℝ)^793 := by
    have hnat : (671031101 : ℕ)^1049*25000000000000^793 ≤ 10978827020217^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671031101 1250000000 10978827020217 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162298009/10000000000 : ℝ)^1049 ≤ (6594469339679/50000000000000 : ℝ)^793 := by
    have hnat : (2162298009 : ℕ)^1049*50000000000000^793 ≤ 6594469339679^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162298009 10000000000 6594469339679 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318440807/2500000000 : ℝ)^1049 ≤ (21447876613021/50000000000000 : ℝ)^793 := by
    have hnat : (1318440807 : ℕ)^1049*50000000000000^793 ≤ 21447876613021^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318440807 2500000000 21447876613021 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671031101/1250000000 : ℝ), (-2162298009/10000000000 : ℝ), (1318440807/2500000000 : ℝ)] ![(10978827020217/25000000000000 : ℝ), (6594469339679/50000000000000 : ℝ), (21447876613021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671031101/1250000000 : ℝ)|^1049 ≤ (10978827020217/25000000000000 : ℝ)^793
        have hw : |(671031101/1250000000 : ℝ)|=(671031101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2162298009/10000000000 : ℝ)|^1049 ≤ (6594469339679/50000000000000 : ℝ)^793
        have hw : |(-2162298009/10000000000 : ℝ)|=(2162298009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318440807/2500000000 : ℝ)|^1049 ≤ (21447876613021/50000000000000 : ℝ)^793
        have hw : |(1318440807/2500000000 : ℝ)|=(1318440807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_14 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (335515557/625000000 : ℝ)*x 0 + (5273763161/10000000000 : ℝ)*x 1 + (-2162297959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335515557/625000000 : ℝ)^1049 ≤ (43915309206299/100000000000000 : ℝ)^793 := by
    have hnat : (335515557 : ℕ)^1049*100000000000000^793 ≤ 43915309206299^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335515557 625000000 43915309206299 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273763161/10000000000 : ℝ)^1049 ≤ (42895752505149/100000000000000 : ℝ)^793 := by
    have hnat : (5273763161 : ℕ)^1049*100000000000000^793 ≤ 42895752505149^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273763161 10000000000 42895752505149 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162297959/10000000000 : ℝ)^1049 ≤ (13188938275929/100000000000000 : ℝ)^793 := by
    have hnat : (2162297959 : ℕ)^1049*100000000000000^793 ≤ 13188938275929^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162297959 10000000000 13188938275929 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335515557/625000000 : ℝ), (5273763161/10000000000 : ℝ), (-2162297959/10000000000 : ℝ)] ![(43915309206299/100000000000000 : ℝ), (42895752505149/100000000000000 : ℝ), (13188938275929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335515557/625000000 : ℝ)|^1049 ≤ (43915309206299/100000000000000 : ℝ)^793
        have hw : |(335515557/625000000 : ℝ)|=(335515557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273763161/10000000000 : ℝ)|^1049 ≤ (42895752505149/100000000000000 : ℝ)^793
        have hw : |(5273763161/10000000000 : ℝ)|=(5273763161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2162297959/10000000000 : ℝ)|^1049 ≤ (13188938275929/100000000000000 : ℝ)^793
        have hw : |(-2162297959/10000000000 : ℝ)|=(2162297959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_box_15 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (528836221/1250000000 : ℝ)*x 0 + (884328373/2000000000 : ℝ)*x 1 + (2210820807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528836221/1250000000 : ℝ)^1049 ≤ (1281939314567/4000000000000 : ℝ)^793 := by
    have hnat : (528836221 : ℕ)^1049*4000000000000^793 ≤ 1281939314567^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528836221 1250000000 1281939314567 4000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884328373/2000000000 : ℝ)^1049 ≤ (6795151966449/20000000000000 : ℝ)^793 := by
    have hnat : (884328373 : ℕ)^1049*20000000000000^793 ≤ 6795151966449^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884328373 2000000000 6795151966449 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210820807/5000000000 : ℝ)^1049 ≤ (2123484830059/6250000000000 : ℝ)^793 := by
    have hnat : (2210820807 : ℕ)^1049*6250000000000^793 ≤ 2123484830059^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210820807 5000000000 2123484830059 6250000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528836221/1250000000 : ℝ), (884328373/2000000000 : ℝ), (2210820807/5000000000 : ℝ)] ![(1281939314567/4000000000000 : ℝ), (6795151966449/20000000000000 : ℝ), (2123484830059/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528836221/1250000000 : ℝ)|^1049 ≤ (1281939314567/4000000000000 : ℝ)^793
        have hw : |(528836221/1250000000 : ℝ)|=(528836221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884328373/2000000000 : ℝ)|^1049 ≤ (6795151966449/20000000000000 : ℝ)^793
        have hw : |(884328373/2000000000 : ℝ)|=(884328373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210820807/5000000000 : ℝ)|^1049 ≤ (2123484830059/6250000000000 : ℝ)^793
        have hw : |(2210820807/5000000000 : ℝ)|=(2210820807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62239/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59343/100000 : ℝ) ∧ (79981/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83251/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11427/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (690494306551339/5000000000000000000 : ℝ) := by
    have hpowers : (11427/100000 : ℝ)^8391 ≤ (690494306551339/5000000000000000000 : ℝ)^2048 := by
      have hnat : (11427 : ℕ)^8391*5000000000000000000^2048 ≤ 690494306551339^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11427 100000 690494306551339 5000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11427/100000 : ℝ)) (X := (690494306551339/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14081/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (32494393871606633/100000000000000000000 : ℝ) := by
    have hpowers : (14081/100000 : ℝ)^8391 ≤ (32494393871606633/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14081 : ℕ)^8391*100000000000000000000^2048 ≤ 32494393871606633^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14081 100000 32494393871606633 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14081/100000 : ℝ)) (X := (32494393871606633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500690494306551339/2500000000000000000 : ℝ) ≤ (10000674048260403/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (2500690494306551339/2500000000000000000 : ℝ)^2048 ≤ (10000674048260403/10000000000000000 : ℝ)^8391 := by
      have hnat : (2500690494306551339 : ℕ)^2048*10000000000000000^8391 ≤ 10000674048260403^8391*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500690494306551339 2500000000000000000 10000674048260403 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674048260403/10000000000000000 : ℝ)) (X := (2500690494306551339/2500000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046304280002633413/100000000000000000000 : ℝ) ≤ (10001129955585577/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (100046304280002633413/100000000000000000000 : ℝ)^2048 ≤ (10001129955585577/10000000000000000 : ℝ)^8391 := by
      have hnat : (100046304280002633413 : ℕ)^2048*10000000000000000^8391 ≤ 10001129955585577^8391*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046304280002633413 100000000000000000000 10001129955585577 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001129955585577/10000000000000000 : ℝ)) (X := (100046304280002633413/100000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032494393871606633/50000000000000000000 : ℝ) ≤ (10001585862910751/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50032494393871606633/50000000000000000000 : ℝ)^2048 ≤ (10001585862910751/10000000000000000 : ℝ)^8391 := by
      have hnat : (50032494393871606633 : ℕ)^2048*10000000000000000^8391 ≤ 10001585862910751^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032494393871606633 50000000000000000000 10001585862910751 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001585862910751/10000000000000000 : ℝ)) (X := (50032494393871606633/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(690494306551339/5000000000000000000 : ℝ) ≤ ((13265684809036791483/13270000000000000000 : ℝ)+2*(227953662587/132700000000000 : ℝ)*(11427/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (13265684809036791483/13270000000000000000 : ℝ)+2*(227953662587/132700000000000 : ℝ)*(11427/100000 : ℝ)=(10000674048260403/10000000000000000 : ℝ) by norm_num, show 1+2*(690494306551339/5000000000000000000 : ℝ)=(2500690494306551339/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32494393871606633/100000000000000000000 : ℝ)+(690494306551339/5000000000000000000 : ℝ) ≤ ((13265684809036791483/13270000000000000000 : ℝ)+(227953662587/132700000000000 : ℝ)*((14081/100000 : ℝ)+(11427/100000 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (13265684809036791483/13270000000000000000 : ℝ)+(227953662587/132700000000000 : ℝ)*((14081/100000 : ℝ)+(11427/100000 : ℝ))=(10001129955585577/10000000000000000 : ℝ) by norm_num, show 1+(32494393871606633/100000000000000000000 : ℝ)+(690494306551339/5000000000000000000 : ℝ)=(100046304280002633413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32494393871606633/100000000000000000000 : ℝ) ≤ ((13265684809036791483/13270000000000000000 : ℝ)+2*(227953662587/132700000000000 : ℝ)*(14081/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (13265684809036791483/13270000000000000000 : ℝ)+2*(227953662587/132700000000000 : ℝ)*(14081/100000 : ℝ)=(10001585862910751/10000000000000000 : ℝ) by norm_num, show 1+2*(32494393871606633/100000000000000000000 : ℝ)=(50032494393871606633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13265684809036791483/13270000000000000000 : ℝ)*(X 1 0+X 2 0)+(227953662587/132700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13265684809036791483/13270000000000000000 : ℝ)) (alpha := (227953662587/132700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13265684809036791483/13270000000000000000 : ℝ)*(X 0 1+X 2 1)+(227953662587/132700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13265684809036791483/13270000000000000000 : ℝ)) (alpha := (227953662587/132700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13265684809036791483/13270000000000000000 : ℝ)*(X 0 2+X 1 2)+(227953662587/132700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13265684809036791483/13270000000000000000 : ℝ)) (alpha := (227953662587/132700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2014876867/10000000000 : ℝ)*X 0 0+(5375484129/10000000000 : ℝ)*X 0 1+(5375483967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1324119141/2500000000 : ℝ)*X 1 0+(-530540413/2500000000 : ℝ)*X 1 1+(5375484027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21185907/40000000 : ℝ)*X 2 0+(53754839/100000000 : ℝ)*X 2 1+(-2122161573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((446365857/1000000000 : ℝ)*X 0 0+(4305300113/10000000000 : ℝ)*X 0 1+(538162549/1250000000 : ℝ)*X 0 2+(446365857/1000000000 : ℝ)*X 1 0+(4305300113/10000000000 : ℝ)*X 1 1+(538162549/1250000000 : ℝ)*X 1 2+(446365857/1000000000 : ℝ)*X 2 0+(4305300113/10000000000 : ℝ)*X 2 1+(538162549/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1133175041/5000000000 : ℝ)*X 0 0+(5281826169/10000000000 : ℝ)*X 0 1+(330114141/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362561193/10000000000 : ℝ)*X 1 0+(-1079584733/5000000000 : ℝ)*X 1 1+(1056365221/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362561743/10000000000 : ℝ)*X 2 0+(2640913099/5000000000 : ℝ)*X 2 1+(-431833721/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265585587/625000000 : ℝ)*X 0 0+(2206212573/5000000000 : ℝ)*X 0 1+(1103105929/2500000000 : ℝ)*X 0 2+(265585587/625000000 : ℝ)*X 1 0+(2206212573/5000000000 : ℝ)*X 1 1+(1103105929/2500000000 : ℝ)*X 1 2+(265585587/625000000 : ℝ)*X 2 0+(2206212573/5000000000 : ℝ)*X 2 1+(1103105929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1106849993/5000000000 : ℝ)*X 0 0+(16306319/31250000 : ℝ)*X 0 1+(5385095979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644845683/5000000000 : ℝ)*X 1 0+(-2118295343/10000000000 : ℝ)*X 1 1+(269254799/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289691349/10000000000 : ℝ)*X 2 0+(5385095981/10000000000 : ℝ)*X 2 1+(-423659073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4485378203/10000000000 : ℝ)*X 0 0+(1073574981/2500000000 : ℝ)*X 0 1+(4294299873/10000000000 : ℝ)*X 0 2+(4485378203/10000000000 : ℝ)*X 1 0+(1073574981/2500000000 : ℝ)*X 1 1+(4294299873/10000000000 : ℝ)*X 1 2+(4485378203/10000000000 : ℝ)*X 2 0+(1073574981/2500000000 : ℝ)*X 2 1+(4294299873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1033905883/5000000000 : ℝ)*X 0 0+(5438050469/10000000000 : ℝ)*X 0 1+(5273763373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671031101/1250000000 : ℝ)*X 1 0+(-2162298009/10000000000 : ℝ)*X 1 1+(1318440807/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((335515557/625000000 : ℝ)*X 2 0+(5273763161/10000000000 : ℝ)*X 2 1+(-2162297959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((528836221/1250000000 : ℝ)*X 0 0+(884328373/2000000000 : ℝ)*X 0 1+(2210820807/5000000000 : ℝ)*X 0 2+(528836221/1250000000 : ℝ)*X 1 0+(884328373/2000000000 : ℝ)*X 1 1+(2210820807/5000000000 : ℝ)*X 1 2+(528836221/1250000000 : ℝ)*X 2 0+(884328373/2000000000 : ℝ)*X 2 1+(2210820807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62239/100000 : ℝ) ≤ (-412939327440757546135264305266049/663500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10569553/6250000000000 : ℝ)*(upper1) + (538922207/100000000000000 : ℝ)*(upper4) + (7083931/6250000000000 : ℝ)*(upper5) + (3967861767170533/100000000000000 : ℝ)*(major0) + (3967861767170533/100000000000000 : ℝ)*(major1) + (3967861767170533/100000000000000 : ℝ)*(major2) + (25876492389/100000000000000 : ℝ)*(sp1) + (796077909/20000000000000 : ℝ)*(sp3) + (5321508139545551/100000000000000 : ℝ)*(sp4) + (332594645364583/6250000000000 : ℝ)*(sp5) + (5321407915672351/100000000000000 : ℝ)*(sp6) + (658731214789653/25000000000000 : ℝ)*(sp7) + (32062780167/100000000000000 : ℝ)*(sp8) + (132286653367/100000000000000 : ℝ)*(sp14) + (2634928839548157/100000000000000 : ℝ)*(f.failure) + (2660770101162859/50000000000000 : ℝ)*(f.sum) + (38730957453021/6635000000000000000000000000 : ℝ)*base65 + (6610510204521929561/1327000000000000000000000000000000 : ℝ)*base68 + (24947781742076929561/1327000000000000000000000000000000 : ℝ)*base70 + (20413139922547929561/1327000000000000000000000000000000 : ℝ)*base72 + (8646330897517/829375000000000000000000000 : ℝ)*base73 + (3070279038914929561/1327000000000000000000000000000000 : ℝ)*base76 + (20589156914166929561/1327000000000000000000000000000000 : ℝ)*base78 + (12616317276183929561/1327000000000000000000000000000000 : ℝ)*base80 + (10716436097131/6635000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2053487/625000000000000000000 : ℝ)*base89 + (2053487/625000000000000000000 : ℝ)*base91 + (2053487/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59343/100000 : ℝ) ≤ (49219672572779486362626397792083/82937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138133163/100000000000000 : ℝ)*(upper0) + (49877409/50000000000000 : ℝ)*(upper2) + (3270023/10000000000000 : ℝ)*(upper3) + (204277217/100000000000000 : ℝ)*(upper4) + (9069403/100000000000000 : ℝ)*(upper5) + (1008226762733567/25000000000000 : ℝ)*(major0) + (1008226762733567/25000000000000 : ℝ)*(major1) + (1008226762733567/25000000000000 : ℝ)*(major2) + (670988619696213/12500000000000 : ℝ)*(sp0) + (5367908444900377/100000000000000 : ℝ)*(sp1) + (5367908302135503/100000000000000 : ℝ)*(sp2) + (1339061655782111/50000000000000 : ℝ)*(sp3) + (655434201/100000000000000 : ℝ)*(sp6) + (512669327/100000000000000 : ℝ)*(sp9) + (1339061655782111/50000000000000 : ℝ)*(f.failure) + (670988619696213/12500000000000 : ℝ)*(f.sum) + (2860852735613/829375000000000000000000000 : ℝ)*base66 + (3115340485391790139/331750000000000000000000000000000 : ℝ)*base68 + (3203893149399290139/331750000000000000000000000000000 : ℝ)*base70 + (858708295890790139/331750000000000000000000000000000 : ℝ)*base72 + (190995555078481/6635000000000000000000000000 : ℝ)*base73 + (194870180603540139/331750000000000000000000000000000 : ℝ)*base76 + (2048109105776040139/331750000000000000000000000000000 : ℝ)*base78 + (985530184104709861/331750000000000000000000000000000 : ℝ)*base79 + (17093505002671/1658750000000000000000000000 : ℝ)*base82 + (4559701/312500000000000000000 : ℝ)*base89 + (4559701/312500000000000000000 : ℝ)*base91 + (4559701/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79981/100000 : ℝ) ≤ (265344927601907325744985577040261/331750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2489873/25000000000000 : ℝ)*(upper1) + (1080309/12500000000000 : ℝ)*(upper2) + (10702537/100000000000000 : ℝ)*(upper3) + (8620183/100000000000000 : ℝ)*(lower5) + (2250127566000263/50000000000000 : ℝ)*(major0) + (2250127566000263/50000000000000 : ℝ)*(major1) + (2250127566000263/50000000000000 : ℝ)*(major2) + (37585123/25000000000000 : ℝ)*(sp0) + (1129384251/50000000000000 : ℝ)*(sp2) + (707680707/20000000000000 : ℝ)*(sp3) + (5985374903436217/100000000000000 : ℝ)*(sp8) + (1496343763444177/25000000000000 : ℝ)*(sp9) + (2992686397504103/50000000000000 : ℝ)*(sp10) + (149423526933909/5000000000000 : ℝ)*(sp11) + (747118519270429/25000000000000 : ℝ)*(f.failure) + (1496343763444177/25000000000000 : ℝ)*(f.sum) + (2404358309811/3317500000000000000000000000 : ℝ)*base65 + (11686230906998239971/663500000000000000000000000000000 : ℝ)*base68 + (7005795391362239971/663500000000000000000000000000000 : ℝ)*base70 + (5869112769950739971/663500000000000000000000000000000 : ℝ)*base72 + (32981078266423/6635000000000000000000000000 : ℝ)*base74 + (3211816556357739971/663500000000000000000000000000000 : ℝ)*base76 + (1979699168941739971/663500000000000000000000000000000 : ℝ)*base78 + (9331479397981239971/663500000000000000000000000000000 : ℝ)*base80 + (17658707465761/3317500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1310439/156250000000000000000 : ℝ)*base89 + (1310439/156250000000000000000 : ℝ)*base91 + (1310439/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83251/100000 : ℝ) ≤ (-552355696713442224558332544544737/663500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112577539/100000000000000 : ℝ)*(upper1) + (9557987/50000000000000 : ℝ)*(lower2) + (5666851/50000000000000 : ℝ)*(upper3) + (103046523/100000000000000 : ℝ)*(upper5) + (4535529782410629/100000000000000 : ℝ)*(major0) + (4535529782410629/100000000000000 : ℝ)*(major1) + (4535529782410629/100000000000000 : ℝ)*(major2) + (503217859/3125000000000 : ℝ)*(sp4) + (1942438031/2500000000000 : ℝ)*(sp6) + (31621664229/25000000000000 : ℝ)*(sp7) + (6086894224198851/100000000000000 : ℝ)*(sp12) + (6086910327170339/100000000000000 : ℝ)*(sp13) + (6086832629649099/100000000000000 : ℝ)*(sp14) + (3011772346407879/100000000000000 : ℝ)*(sp15) + (1505949416532397/50000000000000 : ℝ)*(f.failure) + (6086910327170339/100000000000000 : ℝ)*(f.sum) + (9956100591147/6635000000000000000000000000 : ℝ)*base66 + (12236262707395827193/1327000000000000000000000000000000 : ℝ)*base68 + (21782070715472827193/1327000000000000000000000000000000 : ℝ)*base70 + (6770427196233827193/1327000000000000000000000000000000 : ℝ)*base72 + (23481282089523/6635000000000000000000000000 : ℝ)*base73 + (18464863904179827193/1327000000000000000000000000000000 : ℝ)*base76 + (6575020734825827193/1327000000000000000000000000000000 : ℝ)*base78 + (2877471621231827193/1327000000000000000000000000000000 : ℝ)*base80 + (5668136043889/829375000000000000000000000 : ℝ)*base82 + (3571673/312500000000000000000 : ℝ)*base90 + (3571673/312500000000000000000 : ℝ)*base92 + (3571673/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1199_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59343/100000 : ℝ) else (79981/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83251/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1199_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1199_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59343/100000 : ℝ) else (79981/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83251/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1199_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1199_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59343/100000 : ℝ) else (79981/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83251/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1199_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
