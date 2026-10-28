-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:40.24298+00:00
-- url     : https://prove2.me/submissions/56425f4c-b51d-4270-8ce3-720e8b74a3df

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
theorem support_rectangle_w1204_box_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012706187/10000000000 : ℝ)*x 0 + (5375407617/10000000000 : ℝ)*x 1 + (5375407151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012706187/10000000000 : ℝ)^8397 ≤ (12000531538747/100000000000000 : ℝ)^6349 := by
    have hnat : (2012706187 : ℕ)^8397*100000000000000^6349 ≤ 12000531538747^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012706187 10000000000 12000531538747 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375407617/10000000000 : ℝ)^8397 ≤ (43999736746603/100000000000000 : ℝ)^6349 := by
    have hnat : (5375407617 : ℕ)^8397*100000000000000^6349 ≤ 43999736746603^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375407617 10000000000 43999736746603 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375407151/10000000000 : ℝ)^8397 ≤ (43999731701809/100000000000000 : ℝ)^6349 := by
    have hnat : (5375407151 : ℕ)^8397*100000000000000^6349 ≤ 43999731701809^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375407151 10000000000 43999731701809 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012706187/10000000000 : ℝ), (5375407617/10000000000 : ℝ), (5375407151/10000000000 : ℝ)] ![(12000531538747/100000000000000 : ℝ), (43999736746603/100000000000000 : ℝ), (43999731701809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012706187/10000000000 : ℝ)|^8397 ≤ (12000531538747/100000000000000 : ℝ)^6349
        have hw : |(-2012706187/10000000000 : ℝ)|=(2012706187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375407617/10000000000 : ℝ)|^8397 ≤ (43999736746603/100000000000000 : ℝ)^6349
        have hw : |(5375407617/10000000000 : ℝ)|=(5375407617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375407151/10000000000 : ℝ)|^8397 ≤ (43999731701809/100000000000000 : ℝ)^6349
        have hw : |(5375407151/10000000000 : ℝ)|=(5375407151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648257961/5000000000 : ℝ)*x 0 + (-423968997/2000000000 : ℝ)*x 1 + (5375407371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648257961/5000000000 : ℝ)^8397 ≤ (43147704325719/100000000000000 : ℝ)^6349 := by
    have hnat : (2648257961 : ℕ)^8397*100000000000000^6349 ≤ 43147704325719^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648257961 5000000000 43147704325719 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423968997/2000000000 : ℝ)^8397 ≤ (12852561572529/100000000000000 : ℝ)^6349 := by
    have hnat : (423968997 : ℕ)^8397*100000000000000^6349 ≤ 12852561572529^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423968997 2000000000 12852561572529 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375407371/10000000000 : ℝ)^8397 ≤ (43999734083471/100000000000000 : ℝ)^6349 := by
    have hnat : (5375407371 : ℕ)^8397*100000000000000^6349 ≤ 43999734083471^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375407371 10000000000 43999734083471 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648257961/5000000000 : ℝ), (-423968997/2000000000 : ℝ), (5375407371/10000000000 : ℝ)] ![(43147704325719/100000000000000 : ℝ), (12852561572529/100000000000000 : ℝ), (43999734083471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648257961/5000000000 : ℝ)|^8397 ≤ (43147704325719/100000000000000 : ℝ)^6349
        have hw : |(2648257961/5000000000 : ℝ)|=(2648257961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-423968997/2000000000 : ℝ)|^8397 ≤ (12852561572529/100000000000000 : ℝ)^6349
        have hw : |(-423968997/2000000000 : ℝ)|=(423968997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375407371/10000000000 : ℝ)|^8397 ≤ (43999734083471/100000000000000 : ℝ)^6349
        have hw : |(5375407371/10000000000 : ℝ)|=(5375407371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296516129/10000000000 : ℝ)*x 0 + (2687703599/5000000000 : ℝ)*x 1 + (-2119844941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296516129/10000000000 : ℝ)^8397 ≤ (8629541311197/20000000000000 : ℝ)^6349 := by
    have hnat : (5296516129 : ℕ)^8397*20000000000000^6349 ≤ 8629541311197^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296516129 10000000000 8629541311197 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687703599/5000000000 : ℝ)^8397 ≤ (43999732210619/100000000000000 : ℝ)^6349 := by
    have hnat : (2687703599 : ℕ)^8397*100000000000000^6349 ≤ 43999732210619^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687703599 5000000000 43999732210619 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119844941/10000000000 : ℝ)^8397 ≤ (2570512243941/20000000000000 : ℝ)^6349 := by
    have hnat : (2119844941 : ℕ)^8397*20000000000000^6349 ≤ 2570512243941^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119844941 10000000000 2570512243941 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296516129/10000000000 : ℝ), (2687703599/5000000000 : ℝ), (-2119844941/10000000000 : ℝ)] ![(8629541311197/20000000000000 : ℝ), (43999732210619/100000000000000 : ℝ), (2570512243941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296516129/10000000000 : ℝ)|^8397 ≤ (8629541311197/20000000000000 : ℝ)^6349
        have hw : |(5296516129/10000000000 : ℝ)|=(5296516129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687703599/5000000000 : ℝ)|^8397 ≤ (43999732210619/100000000000000 : ℝ)^6349
        have hw : |(2687703599/5000000000 : ℝ)|=(2687703599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119844941/10000000000 : ℝ)|^8397 ≤ (2570512243941/20000000000000 : ℝ)^6349
        have hw : |(-2119844941/10000000000 : ℝ)|=(2119844941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (892582197/2000000000 : ℝ)*x 0 + (538078837/1250000000 : ℝ)*x 1 + (2152315611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892582197/2000000000 : ℝ)^8397 ≤ (17201463980041/50000000000000 : ℝ)^6349 := by
    have hnat : (892582197 : ℕ)^8397*50000000000000^6349 ≤ 17201463980041^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892582197 2000000000 17201463980041 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538078837/1250000000 : ℝ)^8397 ≤ (4099816670243/12500000000000 : ℝ)^6349 := by
    have hnat : (538078837 : ℕ)^8397*12500000000000^6349 ≤ 4099816670243^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538078837 1250000000 4099816670243 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152315611/5000000000 : ℝ)^8397 ≤ (819963466563/2500000000000 : ℝ)^6349 := by
    have hnat : (2152315611 : ℕ)^8397*2500000000000^6349 ≤ 819963466563^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152315611 5000000000 819963466563 2500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(892582197/2000000000 : ℝ), (538078837/1250000000 : ℝ), (2152315611/5000000000 : ℝ)] ![(17201463980041/50000000000000 : ℝ), (4099816670243/12500000000000 : ℝ), (819963466563/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(892582197/2000000000 : ℝ)|^8397 ≤ (17201463980041/50000000000000 : ℝ)^6349
        have hw : |(892582197/2000000000 : ℝ)|=(892582197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538078837/1250000000 : ℝ)|^8397 ≤ (4099816670243/12500000000000 : ℝ)^6349
        have hw : |(538078837/1250000000 : ℝ)|=(538078837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2152315611/5000000000 : ℝ)|^8397 ≤ (819963466563/2500000000000 : ℝ)^6349
        have hw : |(2152315611/5000000000 : ℝ)|=(2152315611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2263851523/10000000000 : ℝ)*x 0 + (2640941451/5000000000 : ℝ)*x 1 + (2640941383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2263851523/10000000000 : ℝ)^8397 ≤ (14019771255093/100000000000000 : ℝ)^6349 := by
    have hnat : (2263851523 : ℕ)^8397*100000000000000^6349 ≤ 14019771255093^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263851523 10000000000 14019771255093 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640941451/5000000000 : ℝ)^8397 ≤ (21495057550033/50000000000000 : ℝ)^6349 := by
    have hnat : (2640941451 : ℕ)^8397*50000000000000^6349 ≤ 21495057550033^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640941451 5000000000 21495057550033 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640941383/5000000000 : ℝ)^8397 ≤ (42990113636077/100000000000000 : ℝ)^6349 := by
    have hnat : (2640941383 : ℕ)^8397*100000000000000^6349 ≤ 42990113636077^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640941383 5000000000 42990113636077 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2263851523/10000000000 : ℝ), (2640941451/5000000000 : ℝ), (2640941383/5000000000 : ℝ)] ![(14019771255093/100000000000000 : ℝ), (21495057550033/50000000000000 : ℝ), (42990113636077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2263851523/10000000000 : ℝ)|^8397 ≤ (14019771255093/100000000000000 : ℝ)^6349
        have hw : |(-2263851523/10000000000 : ℝ)|=(2263851523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640941451/5000000000 : ℝ)|^8397 ≤ (21495057550033/50000000000000 : ℝ)^6349
        have hw : |(2640941451/5000000000 : ℝ)|=(2640941451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640941383/5000000000 : ℝ)|^8397 ≤ (42990113636077/100000000000000 : ℝ)^6349
        have hw : |(2640941383/5000000000 : ℝ)|=(2640941383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681249931/5000000000 : ℝ)*x 0 + (-215681381/1000000000 : ℝ)*x 1 + (1056376499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681249931/5000000000 : ℝ)^8397 ≤ (43860054923593/100000000000000 : ℝ)^6349 := by
    have hnat : (2681249931 : ℕ)^8397*100000000000000^6349 ≤ 43860054923593^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681249931 5000000000 43860054923593 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215681381/1000000000 : ℝ)^8397 ≤ (3287458586241/25000000000000 : ℝ)^6349 := by
    have hnat : (215681381 : ℕ)^8397*25000000000000^6349 ≤ 3287458586241^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215681381 1000000000 3287458586241 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056376499/2000000000 : ℝ)^8397 ≤ (21495055359433/50000000000000 : ℝ)^6349 := by
    have hnat : (1056376499 : ℕ)^8397*50000000000000^6349 ≤ 21495055359433^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056376499 2000000000 21495055359433 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681249931/5000000000 : ℝ), (-215681381/1000000000 : ℝ), (1056376499/2000000000 : ℝ)] ![(43860054923593/100000000000000 : ℝ), (3287458586241/25000000000000 : ℝ), (21495055359433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681249931/5000000000 : ℝ)|^8397 ≤ (43860054923593/100000000000000 : ℝ)^6349
        have hw : |(2681249931/5000000000 : ℝ)|=(2681249931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215681381/1000000000 : ℝ)|^8397 ≤ (3287458586241/25000000000000 : ℝ)^6349
        have hw : |(-215681381/1000000000 : ℝ)|=(215681381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056376499/2000000000 : ℝ)|^8397 ≤ (21495055359433/50000000000000 : ℝ)^6349
        have hw : |(1056376499/2000000000 : ℝ)|=(1056376499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362499433/10000000000 : ℝ)*x 0 + (660235373/1250000000 : ℝ)*x 1 + (-2156813731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362499433/10000000000 : ℝ)^8397 ≤ (5482506285369/12500000000000 : ℝ)^6349 := by
    have hnat : (5362499433 : ℕ)^8397*12500000000000^6349 ≤ 5482506285369^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362499433 10000000000 5482506285369 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660235373/1250000000 : ℝ)^8397 ≤ (10747528995691/25000000000000 : ℝ)^6349 := by
    have hnat : (660235373 : ℕ)^8397*25000000000000^6349 ≤ 10747528995691^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660235373 1250000000 10747528995691 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156813731/10000000000 : ℝ)^8397 ≤ (1643729213493/12500000000000 : ℝ)^6349 := by
    have hnat : (2156813731 : ℕ)^8397*12500000000000^6349 ≤ 1643729213493^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156813731 10000000000 1643729213493 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362499433/10000000000 : ℝ), (660235373/1250000000 : ℝ), (-2156813731/10000000000 : ℝ)] ![(5482506285369/12500000000000 : ℝ), (10747528995691/25000000000000 : ℝ), (1643729213493/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362499433/10000000000 : ℝ)|^8397 ≤ (5482506285369/12500000000000 : ℝ)^6349
        have hw : |(5362499433/10000000000 : ℝ)|=(5362499433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660235373/1250000000 : ℝ)|^8397 ≤ (10747528995691/25000000000000 : ℝ)^6349
        have hw : |(660235373/1250000000 : ℝ)|=(660235373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2156813731/10000000000 : ℝ)|^8397 ≤ (1643729213493/12500000000000 : ℝ)^6349
        have hw : |(-2156813731/10000000000 : ℝ)|=(2156813731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4248728633/10000000000 : ℝ)*x 0 + (441170159/1000000000 : ℝ)*x 1 + (275731371/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248728633/10000000000 : ℝ)^8397 ≤ (32236383766317/100000000000000 : ℝ)^6349 := by
    have hnat : (4248728633 : ℕ)^8397*100000000000000^6349 ≤ 32236383766317^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248728633 10000000000 32236383766317 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441170159/1000000000 : ℝ)^8397 ≤ (33881806352447/100000000000000 : ℝ)^6349 := by
    have hnat : (441170159 : ℕ)^8397*100000000000000^6349 ≤ 33881806352447^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441170159 1000000000 33881806352447 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275731371/625000000 : ℝ)^8397 ≤ (33881809866881/100000000000000 : ℝ)^6349 := by
    have hnat : (275731371 : ℕ)^8397*100000000000000^6349 ≤ 33881809866881^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275731371 625000000 33881809866881 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248728633/10000000000 : ℝ), (441170159/1000000000 : ℝ), (275731371/625000000 : ℝ)] ![(32236383766317/100000000000000 : ℝ), (33881806352447/100000000000000 : ℝ), (33881809866881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248728633/10000000000 : ℝ)|^8397 ≤ (32236383766317/100000000000000 : ℝ)^6349
        have hw : |(4248728633/10000000000 : ℝ)|=(4248728633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441170159/1000000000 : ℝ)|^8397 ≤ (33881806352447/100000000000000 : ℝ)^6349
        have hw : |(441170159/1000000000 : ℝ)|=(441170159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275731371/625000000 : ℝ)|^8397 ≤ (33881809866881/100000000000000 : ℝ)^6349
        have hw : |(275731371/625000000 : ℝ)|=(275731371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_8 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-442252937/2000000000 : ℝ)*x 0 + (208726377/400000000 : ℝ)*x 1 + (5385019811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442252937/2000000000 : ℝ)^8397 ≤ (2718135916079/20000000000000 : ℝ)^6349 := by
    have hnat : (442252937 : ℕ)^8397*20000000000000^6349 ≤ 2718135916079^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442252937 2000000000 2718135916079 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208726377/400000000 : ℝ)^8397 ≤ (8461098912229/20000000000000 : ℝ)^6349 := by
    have hnat : (208726377 : ℕ)^8397*20000000000000^6349 ≤ 8461098912229^6349*400000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208726377 400000000 8461098912229 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385019811/10000000000 : ℝ)^8397 ≤ (22051912918603/50000000000000 : ℝ)^6349 := by
    have hnat : (5385019811 : ℕ)^8397*50000000000000^6349 ≤ 22051912918603^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385019811 10000000000 22051912918603 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442252937/2000000000 : ℝ), (208726377/400000000 : ℝ), (5385019811/10000000000 : ℝ)] ![(2718135916079/20000000000000 : ℝ), (8461098912229/20000000000000 : ℝ), (22051912918603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442252937/2000000000 : ℝ)|^8397 ≤ (2718135916079/20000000000000 : ℝ)^6349
        have hw : |(-442252937/2000000000 : ℝ)|=(442252937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208726377/400000000 : ℝ)|^8397 ≤ (8461098912229/20000000000000 : ℝ)^6349
        have hw : |(208726377/400000000 : ℝ)|=(208726377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385019811/10000000000 : ℝ)|^8397 ≤ (22051912918603/50000000000000 : ℝ)^6349
        have hw : |(5385019811/10000000000 : ℝ)|=(5385019811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_9 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057946423/2000000000 : ℝ)*x 0 + (-528994153/2500000000 : ℝ)*x 1 + (5385019227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057946423/2000000000 : ℝ)^8397 ≤ (21537314566277/50000000000000 : ℝ)^6349 := by
    have hnat : (1057946423 : ℕ)^8397*50000000000000^6349 ≤ 21537314566277^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057946423 2000000000 21537314566277 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528994153/2500000000 : ℝ)^8397 ≤ (3205387837803/25000000000000 : ℝ)^6349 := by
    have hnat : (528994153 : ℕ)^8397*25000000000000^6349 ≤ 3205387837803^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528994153 2500000000 3205387837803 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385019227/10000000000 : ℝ)^8397 ≤ (44103819511331/100000000000000 : ℝ)^6349 := by
    have hnat : (5385019227 : ℕ)^8397*100000000000000^6349 ≤ 44103819511331^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385019227 10000000000 44103819511331 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057946423/2000000000 : ℝ), (-528994153/2500000000 : ℝ), (5385019227/10000000000 : ℝ)] ![(21537314566277/50000000000000 : ℝ), (3205387837803/25000000000000 : ℝ), (44103819511331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057946423/2000000000 : ℝ)|^8397 ≤ (21537314566277/50000000000000 : ℝ)^6349
        have hw : |(1057946423/2000000000 : ℝ)|=(1057946423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528994153/2500000000 : ℝ)|^8397 ≤ (3205387837803/25000000000000 : ℝ)^6349
        have hw : |(-528994153/2500000000 : ℝ)|=(528994153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385019227/10000000000 : ℝ)|^8397 ≤ (44103819511331/100000000000000 : ℝ)^6349
        have hw : |(5385019227/10000000000 : ℝ)|=(5385019227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_10 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289732731/10000000000 : ℝ)*x 0 + (2692508781/5000000000 : ℝ)*x 1 + (-132248627/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289732731/10000000000 : ℝ)^8397 ≤ (2692164735421/6250000000000 : ℝ)^6349 := by
    have hnat : (5289732731 : ℕ)^8397*6250000000000^6349 ≤ 2692164735421^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289732731 10000000000 2692164735421 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692508781/5000000000 : ℝ)^8397 ≤ (44103801476089/100000000000000 : ℝ)^6349 := by
    have hnat : (2692508781 : ℕ)^8397*100000000000000^6349 ≤ 44103801476089^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692508781 5000000000 44103801476089 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132248627/625000000 : ℝ)^8397 ≤ (12821562731073/100000000000000 : ℝ)^6349 := by
    have hnat : (132248627 : ℕ)^8397*100000000000000^6349 ≤ 12821562731073^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132248627 625000000 12821562731073 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289732731/10000000000 : ℝ), (2692508781/5000000000 : ℝ), (-132248627/625000000 : ℝ)] ![(2692164735421/6250000000000 : ℝ), (44103801476089/100000000000000 : ℝ), (12821562731073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289732731/10000000000 : ℝ)|^8397 ≤ (2692164735421/6250000000000 : ℝ)^6349
        have hw : |(5289732731/10000000000 : ℝ)|=(5289732731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692508781/5000000000 : ℝ)|^8397 ≤ (44103801476089/100000000000000 : ℝ)^6349
        have hw : |(2692508781/5000000000 : ℝ)|=(2692508781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132248627/625000000 : ℝ)|^8397 ≤ (12821562731073/100000000000000 : ℝ)^6349
        have hw : |(-132248627/625000000 : ℝ)|=(132248627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_11 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2242325307/5000000000 : ℝ)*x 0 + (85872397/200000000 : ℝ)*x 1 + (2146810693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242325307/5000000000 : ℝ)^8397 ≤ (6924948379447/20000000000000 : ℝ)^6349 := by
    have hnat : (2242325307 : ℕ)^8397*20000000000000^6349 ≤ 6924948379447^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242325307 5000000000 6924948379447 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85872397/200000000 : ℝ)^8397 ≤ (32687621312477/100000000000000 : ℝ)^6349 := by
    have hnat : (85872397 : ℕ)^8397*100000000000000^6349 ≤ 32687621312477^6349*200000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85872397 200000000 32687621312477 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2146810693/5000000000 : ℝ)^8397 ≤ (4085954597273/12500000000000 : ℝ)^6349 := by
    have hnat : (2146810693 : ℕ)^8397*12500000000000^6349 ≤ 4085954597273^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146810693 5000000000 4085954597273 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242325307/5000000000 : ℝ), (85872397/200000000 : ℝ), (2146810693/5000000000 : ℝ)] ![(6924948379447/20000000000000 : ℝ), (32687621312477/100000000000000 : ℝ), (4085954597273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242325307/5000000000 : ℝ)|^8397 ≤ (6924948379447/20000000000000 : ℝ)^6349
        have hw : |(2242325307/5000000000 : ℝ)|=(2242325307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85872397/200000000 : ℝ)|^8397 ≤ (32687621312477/100000000000000 : ℝ)^6349
        have hw : |(85872397/200000000 : ℝ)|=(85872397/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2146810693/5000000000 : ℝ)|^8397 ≤ (4085954597273/12500000000000 : ℝ)^6349
        have hw : |(2146810693/5000000000 : ℝ)|=(2146810693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_12 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-413114977/2000000000 : ℝ)*x 0 + (5437895843/10000000000 : ℝ)*x 1 + (527381831/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413114977/2000000000 : ℝ)^8397 ≤ (12419192839997/100000000000000 : ℝ)^6349 := by
    have hnat : (413114977 : ℕ)^8397*100000000000000^6349 ≤ 12419192839997^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413114977 2000000000 12419192839997 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437895843/10000000000 : ℝ)^8397 ≤ (44677482923989/100000000000000 : ℝ)^6349 := by
    have hnat : (5437895843 : ℕ)^8397*100000000000000^6349 ≤ 44677482923989^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437895843 10000000000 44677482923989 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527381831/1000000000 : ℝ)^8397 ≤ (8580664844973/20000000000000 : ℝ)^6349 := by
    have hnat : (527381831 : ℕ)^8397*20000000000000^6349 ≤ 8580664844973^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527381831 1000000000 8580664844973 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413114977/2000000000 : ℝ), (5437895843/10000000000 : ℝ), (527381831/1000000000 : ℝ)] ![(12419192839997/100000000000000 : ℝ), (44677482923989/100000000000000 : ℝ), (8580664844973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413114977/2000000000 : ℝ)|^8397 ≤ (12419192839997/100000000000000 : ℝ)^6349
        have hw : |(-413114977/2000000000 : ℝ)|=(413114977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437895843/10000000000 : ℝ)|^8397 ≤ (44677482923989/100000000000000 : ℝ)^6349
        have hw : |(5437895843/10000000000 : ℝ)|=(5437895843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527381831/1000000000 : ℝ)|^8397 ≤ (8580664844973/20000000000000 : ℝ)^6349
        have hw : |(527381831/1000000000 : ℝ)|=(527381831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_13 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368187269/10000000000 : ℝ)*x 0 + (-1687457/7812500 : ℝ)*x 1 + (5273818237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368187269/10000000000 : ℝ)^8397 ≤ (21960794045903/50000000000000 : ℝ)^6349 := by
    have hnat : (5368187269 : ℕ)^8397*50000000000000^6349 ≤ 21960794045903^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368187269 10000000000 21960794045903 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1687457/7812500 : ℝ)^8397 ≤ (13175088449191/100000000000000 : ℝ)^6349 := by
    have hnat : (1687457 : ℕ)^8397*100000000000000^6349 ≤ 13175088449191^6349*7812500^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687457 7812500 13175088449191 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273818237/10000000000 : ℝ)^8397 ≤ (8580664687887/20000000000000 : ℝ)^6349 := by
    have hnat : (5273818237 : ℕ)^8397*20000000000000^6349 ≤ 8580664687887^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273818237 10000000000 8580664687887 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368187269/10000000000 : ℝ), (-1687457/7812500 : ℝ), (5273818237/10000000000 : ℝ)] ![(21960794045903/50000000000000 : ℝ), (13175088449191/100000000000000 : ℝ), (8580664687887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368187269/10000000000 : ℝ)|^8397 ≤ (21960794045903/50000000000000 : ℝ)^6349
        have hw : |(5368187269/10000000000 : ℝ)|=(5368187269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1687457/7812500 : ℝ)|^8397 ≤ (13175088449191/100000000000000 : ℝ)^6349
        have hw : |(-1687457/7812500 : ℝ)|=(1687457/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273818237/10000000000 : ℝ)|^8397 ≤ (8580664687887/20000000000000 : ℝ)^6349
        have hw : |(5273818237/10000000000 : ℝ)|=(5273818237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_14 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368187531/10000000000 : ℝ)*x 0 + (5273818129/10000000000 : ℝ)*x 1 + (-1079972377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368187531/10000000000 : ℝ)^8397 ≤ (1098039773173/2500000000000 : ℝ)^6349 := by
    have hnat : (5368187531 : ℕ)^8397*2500000000000^6349 ≤ 1098039773173^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368187531 10000000000 1098039773173 2500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273818129/10000000000 : ℝ)^8397 ≤ (42903322277429/100000000000000 : ℝ)^6349 := by
    have hnat : (5273818129 : ℕ)^8397*100000000000000^6349 ≤ 42903322277429^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273818129 10000000000 42903322277429 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079972377/5000000000 : ℝ)^8397 ≤ (13175086787321/100000000000000 : ℝ)^6349 := by
    have hnat : (1079972377 : ℕ)^8397*100000000000000^6349 ≤ 13175086787321^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079972377 5000000000 13175086787321 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368187531/10000000000 : ℝ), (5273818129/10000000000 : ℝ), (-1079972377/5000000000 : ℝ)] ![(1098039773173/2500000000000 : ℝ), (42903322277429/100000000000000 : ℝ), (13175086787321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368187531/10000000000 : ℝ)|^8397 ≤ (1098039773173/2500000000000 : ℝ)^6349
        have hw : |(5368187531/10000000000 : ℝ)|=(5368187531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273818129/10000000000 : ℝ)|^8397 ≤ (42903322277429/100000000000000 : ℝ)^6349
        have hw : |(5273818129/10000000000 : ℝ)|=(5273818129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079972377/5000000000 : ℝ)|^8397 ≤ (13175086787321/100000000000000 : ℝ)^6349
        have hw : |(-1079972377/5000000000 : ℝ)|=(1079972377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_box_15 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4230028023/10000000000 : ℝ)*x 0 + (221046493/500000000 : ℝ)*x 1 + (4420929239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4230028023/10000000000 : ℝ)^8397 ≤ (32048861343819/100000000000000 : ℝ)^6349 := by
    have hnat : (4230028023 : ℕ)^8397*100000000000000^6349 ≤ 32048861343819^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230028023 10000000000 32048861343819 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221046493/500000000 : ℝ)^8397 ≤ (16987786238949/50000000000000 : ℝ)^6349 := by
    have hnat : (221046493 : ℕ)^8397*50000000000000^6349 ≤ 16987786238949^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221046493 500000000 16987786238949 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420929239/10000000000 : ℝ)^8397 ≤ (8493891541487/25000000000000 : ℝ)^6349 := by
    have hnat : (4420929239 : ℕ)^8397*25000000000000^6349 ≤ 8493891541487^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420929239 10000000000 8493891541487 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4230028023/10000000000 : ℝ), (221046493/500000000 : ℝ), (4420929239/10000000000 : ℝ)] ![(32048861343819/100000000000000 : ℝ), (16987786238949/50000000000000 : ℝ), (8493891541487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4230028023/10000000000 : ℝ)|^8397 ≤ (32048861343819/100000000000000 : ℝ)^6349
        have hw : |(4230028023/10000000000 : ℝ)|=(4230028023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221046493/500000000 : ℝ)|^8397 ≤ (16987786238949/50000000000000 : ℝ)^6349
        have hw : |(221046493/500000000 : ℝ)|=(221046493/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420929239/10000000000 : ℝ)|^8397 ≤ (8493891541487/25000000000000 : ℝ)^6349
        have hw : |(4420929239/10000000000 : ℝ)|=(4420929239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(389/625 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59347/100000 : ℝ) ∧ (19999/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41631/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11433/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (13766538082185959/100000000000000000000 : ℝ) := by
    have hpowers : (11433/100000 : ℝ)^2099 ≤ (13766538082185959/100000000000000000000 : ℝ)^512 := by
      have hnat : (11433 : ℕ)^2099*100000000000000000000^512 ≤ 13766538082185959^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11433 100000 13766538082185959 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11433/100000 : ℝ)) (X := (13766538082185959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (32358082355915869/100000000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^2099 ≤ (32358082355915869/100000000000000000000 : ℝ)^512 := by
      have hnat : (14083 : ℕ)^2099*100000000000000000000^512 ≤ 32358082355915869^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 32358082355915869 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (32358082355915869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013766538082185959/50000000000000000000 : ℝ) ≤ (10000671532536897/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50013766538082185959/50000000000000000000 : ℝ)^512 ≤ (10000671532536897/10000000000000000 : ℝ)^2099 := by
      have hnat : (50013766538082185959 : ℕ)^512*10000000000000000^2099 ≤ 10000671532536897^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013766538082185959 50000000000000000000 10000671532536897 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000671532536897/10000000000000000 : ℝ)) (X := (50013766538082185959/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011531155109525457/25000000000000000000 : ℝ) ≤ (625070306362941/625000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (25011531155109525457/25000000000000000000 : ℝ)^512 ≤ (625070306362941/625000000000000 : ℝ)^2099 := by
      have hnat : (25011531155109525457 : ℕ)^512*625000000000000^2099 ≤ 625070306362941^2099*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011531155109525457 25000000000000000000 625070306362941 625000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625070306362941/625000000000000 : ℝ)) (X := (25011531155109525457/25000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032358082355915869/50000000000000000000 : ℝ) ≤ (2000315654215443/2000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50032358082355915869/50000000000000000000 : ℝ)^512 ≤ (2000315654215443/2000000000000000 : ℝ)^2099 := by
      have hnat : (50032358082355915869 : ℕ)^512*2000000000000000^2099 ≤ 2000315654215443^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032358082355915869 50000000000000000000 2000315654215443 2000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000315654215443/2000000000000000 : ℝ)) (X := (50032358082355915869/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13766538082185959/100000000000000000000 : ℝ) ≤ ((6622853204872830339/6625000000000000000 : ℝ)+2*(453369270159/265000000000000 : ℝ)*(11433/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (6622853204872830339/6625000000000000000 : ℝ)+2*(453369270159/265000000000000 : ℝ)*(11433/100000 : ℝ)=(10000671532536897/10000000000000000 : ℝ) by norm_num, show 1+2*(13766538082185959/100000000000000000000 : ℝ)=(50013766538082185959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32358082355915869/100000000000000000000 : ℝ)+(13766538082185959/100000000000000000000 : ℝ) ≤ ((6622853204872830339/6625000000000000000 : ℝ)+(453369270159/265000000000000 : ℝ)*((14083/100000 : ℝ)+(11433/100000 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (6622853204872830339/6625000000000000000 : ℝ)+(453369270159/265000000000000 : ℝ)*((14083/100000 : ℝ)+(11433/100000 : ℝ))=(625070306362941/625000000000000 : ℝ) by norm_num, show 1+(32358082355915869/100000000000000000000 : ℝ)+(13766538082185959/100000000000000000000 : ℝ)=(25011531155109525457/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32358082355915869/100000000000000000000 : ℝ) ≤ ((6622853204872830339/6625000000000000000 : ℝ)+2*(453369270159/265000000000000 : ℝ)*(14083/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (6622853204872830339/6625000000000000000 : ℝ)+2*(453369270159/265000000000000 : ℝ)*(14083/100000 : ℝ)=(2000315654215443/2000000000000000 : ℝ) by norm_num, show 1+2*(32358082355915869/100000000000000000000 : ℝ)=(50032358082355915869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6622853204872830339/6625000000000000000 : ℝ)*(X 1 0+X 2 0)+(453369270159/265000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (6622853204872830339/6625000000000000000 : ℝ)) (alpha := (453369270159/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6622853204872830339/6625000000000000000 : ℝ)*(X 0 1+X 2 1)+(453369270159/265000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (6622853204872830339/6625000000000000000 : ℝ)) (alpha := (453369270159/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6622853204872830339/6625000000000000000 : ℝ)*(X 0 2+X 1 2)+(453369270159/265000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (6622853204872830339/6625000000000000000 : ℝ)) (alpha := (453369270159/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2012706187/10000000000 : ℝ)*X 0 0+(5375407617/10000000000 : ℝ)*X 0 1+(5375407151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648257961/5000000000 : ℝ)*X 1 0+(-423968997/2000000000 : ℝ)*X 1 1+(5375407371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296516129/10000000000 : ℝ)*X 2 0+(2687703599/5000000000 : ℝ)*X 2 1+(-2119844941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((892582197/2000000000 : ℝ)*X 0 0+(538078837/1250000000 : ℝ)*X 0 1+(2152315611/5000000000 : ℝ)*X 0 2+(892582197/2000000000 : ℝ)*X 1 0+(538078837/1250000000 : ℝ)*X 1 1+(2152315611/5000000000 : ℝ)*X 1 2+(892582197/2000000000 : ℝ)*X 2 0+(538078837/1250000000 : ℝ)*X 2 1+(2152315611/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2263851523/10000000000 : ℝ)*X 0 0+(2640941451/5000000000 : ℝ)*X 0 1+(2640941383/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681249931/5000000000 : ℝ)*X 1 0+(-215681381/1000000000 : ℝ)*X 1 1+(1056376499/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362499433/10000000000 : ℝ)*X 2 0+(660235373/1250000000 : ℝ)*X 2 1+(-2156813731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4248728633/10000000000 : ℝ)*X 0 0+(441170159/1000000000 : ℝ)*X 0 1+(275731371/625000000 : ℝ)*X 0 2+(4248728633/10000000000 : ℝ)*X 1 0+(441170159/1000000000 : ℝ)*X 1 1+(275731371/625000000 : ℝ)*X 1 2+(4248728633/10000000000 : ℝ)*X 2 0+(441170159/1000000000 : ℝ)*X 2 1+(275731371/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-442252937/2000000000 : ℝ)*X 0 0+(208726377/400000000 : ℝ)*X 0 1+(5385019811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057946423/2000000000 : ℝ)*X 1 0+(-528994153/2500000000 : ℝ)*X 1 1+(5385019227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289732731/10000000000 : ℝ)*X 2 0+(2692508781/5000000000 : ℝ)*X 2 1+(-132248627/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2242325307/5000000000 : ℝ)*X 0 0+(85872397/200000000 : ℝ)*X 0 1+(2146810693/5000000000 : ℝ)*X 0 2+(2242325307/5000000000 : ℝ)*X 1 0+(85872397/200000000 : ℝ)*X 1 1+(2146810693/5000000000 : ℝ)*X 1 2+(2242325307/5000000000 : ℝ)*X 2 0+(85872397/200000000 : ℝ)*X 2 1+(2146810693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-413114977/2000000000 : ℝ)*X 0 0+(5437895843/10000000000 : ℝ)*X 0 1+(527381831/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368187269/10000000000 : ℝ)*X 1 0+(-1687457/7812500 : ℝ)*X 1 1+(5273818237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368187531/10000000000 : ℝ)*X 2 0+(5273818129/10000000000 : ℝ)*X 2 1+(-1079972377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4230028023/10000000000 : ℝ)*X 0 0+(221046493/500000000 : ℝ)*X 0 1+(4420929239/10000000000 : ℝ)*X 0 2+(4230028023/10000000000 : ℝ)*X 1 0+(221046493/500000000 : ℝ)*X 1 1+(4420929239/10000000000 : ℝ)*X 1 2+(4230028023/10000000000 : ℝ)*X 2 0+(221046493/500000000 : ℝ)*X 2 1+(4420929239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-389/625 : ℝ) ≤ (-51540259539272118228896800181691/82812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14567621/25000000000000 : ℝ)*(upper0) + (28194279/100000000000000 : ℝ)*(upper1) + (94490049/100000000000000 : ℝ)*(upper2) + (7388231/10000000000000 : ℝ)*(upper3) + (25491953/25000000000000 : ℝ)*(upper5) + (993030201857423/25000000000000 : ℝ)*(major0) + (993030201857423/25000000000000 : ℝ)*(major1) + (993030201857423/25000000000000 : ℝ)*(major2) + (4065278797/20000000000000 : ℝ)*(sp1) + (10250850553/100000000000000 : ℝ)*(sp3) + (1332235457597439/25000000000000 : ℝ)*(sp4) + (532892150399577/10000000000000 : ℝ)*(sp5) + (1332235457597439/25000000000000 : ℝ)*(sp6) + (329504412308131/12500000000000 : ℝ)*(sp7) + (1318022774657801/50000000000000 : ℝ)*(f.failure) + (1332235457597439/25000000000000 : ℝ)*(f.sum) + (29312407811389/6625000000000000000000000000 : ℝ)*base65 + (1813747360453181397/165625000000000000000000000000000 : ℝ)*base67 + (1469501719265568603/165625000000000000000000000000000 : ℝ)*base70 + (1764638905493806397/165625000000000000000000000000000 : ℝ)*base71 + (254169832955639/6625000000000000000000000000 : ℝ)*base73 + (10843596662243806397/165625000000000000000000000000000 : ℝ)*base75 + (98293776424943603/165625000000000000000000000000000 : ℝ)*base78 + (10079766486778181397/165625000000000000000000000000000 : ℝ)*base79 + (1166621520079/414062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (36701/156250000000000000000 : ℝ)*base89 + (36701/156250000000000000000 : ℝ)*base91 + (36701/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59347/100000 : ℝ) ≤ (12287209416446371288245138299877/20703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131681567/50000000000000 : ℝ)*(upper0) + (13958499/12500000000000 : ℝ)*(upper3) + (16785497/12500000000000 : ℝ)*(upper4) + (126164692181549/3125000000000 : ℝ)*(major0) + (126164692181549/3125000000000 : ℝ)*(major1) + (126164692181549/3125000000000 : ℝ)*(major2) + (43003808036147/800000000000 : ℝ)*(sp0) + (5375475370892429/100000000000000 : ℝ)*(sp1) + (5375471883394123/100000000000000 : ℝ)*(sp2) + (2679224437839329/100000000000000 : ℝ)*(sp3) + (87281089/12500000000000 : ℝ)*(sp5) + (4185747017/100000000000000 : ℝ)*(sp6) + (12924553/20000000000000 : ℝ)*(sp8) + (56612697707/100000000000000 : ℝ)*(sp11) + (669820262634259/25000000000000 : ℝ)*(f.failure) + (5375476069141141/100000000000000 : ℝ)*(f.sum) + (8759382920469/6625000000000000000000000000 : ℝ)*base66 + (164973445000958861/20703125000000000000000000000000 : ℝ)*base67 + (112249012993927611/20703125000000000000000000000000 : ℝ)*base69 + (126335899730362243/10351562500000000000000000000000 : ℝ)*base71 + (203294986133969/6625000000000000000000000000 : ℝ)*base74 + (14778267316281967/2587890625000000000000000000000 : ℝ)*base75 + (74617715086079559/5175781250000000000000000000000 : ℝ)*base77 + (574473316154865111/20703125000000000000000000000000 : ℝ)*base79 + (10702885467797/3312500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (160641/78125000000000000000 : ℝ)*base90 + (160641/78125000000000000000 : ℝ)*base92 + (160641/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (19999/25000 : ℝ) ≤ (66248678981224841950555954657863/82812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1077887749/100000000000000 : ℝ)*(upper0) + (47839223/100000000000000 : ℝ)*(lower3) + (1307071819/100000000000000 : ℝ)*(lower5) + (2252269275282139/50000000000000 : ℝ)*(major0) + (2252269275282139/50000000000000 : ℝ)*(major1) + (2252269275282139/50000000000000 : ℝ)*(major2) + (272097111479/50000000000000 : ℝ)*(sp1) + (169513438039/100000000000000 : ℝ)*(sp3) + (43315318979/100000000000000 : ℝ)*(sp4) + (5992956057353599/100000000000000 : ℝ)*(sp8) + (5992489214337223/100000000000000 : ℝ)*(sp9) + (5993033408560181/100000000000000 : ℝ)*(sp10) + (298920804419449/10000000000000 : ℝ)*(sp11) + (8508971901/25000000000000 : ℝ)*(sp12) + (186836097352033/6250000000000 : ℝ)*(f.failure) + (5993033408560181/100000000000000 : ℝ)*(f.sum) + (8751018327387/3312500000000000000000000000 : ℝ)*base66 + (416771041975290121/331250000000000000000000000000000 : ℝ)*base67 + (978650154749709879/331250000000000000000000000000000 : ℝ)*base70 + (2093643436718459879/331250000000000000000000000000000 : ℝ)*base72 + (67511075299149/6625000000000000000000000000 : ℝ)*base74 + (670658905299709879/331250000000000000000000000000000 : ℝ)*base76 + (2296047253405959879/331250000000000000000000000000000 : ℝ)*base78 + (8916645199280959879/331250000000000000000000000000000 : ℝ)*base80 + (7733054725351/6625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (571/9765625000000000000 : ℝ)*base90 + (571/9765625000000000000 : ℝ)*base92 + (571/9765625000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41631/50000 : ℝ) ≤ (-137898972795050318979276825053337/165625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2716589/20000000000000 : ℝ)*(lower0) + (17338979/12500000000000 : ℝ)*(upper1) + (79840229/50000000000000 : ℝ)*(lower2) + (41818263/50000000000000 : ℝ)*(upper3) + (43600821/25000000000000 : ℝ)*(upper5) + (4539874112521461/100000000000000 : ℝ)*(major0) + (4539874112521461/100000000000000 : ℝ)*(major1) + (4539874112521461/100000000000000 : ℝ)*(major2) + (13124484177/100000000000000 : ℝ)*(sp4) + (94557935093/50000000000000 : ℝ)*(sp7) + (6094660815982797/100000000000000 : ℝ)*(sp12) + (243786957618679/4000000000000 : ℝ)*(sp13) + (243786957618679/4000000000000 : ℝ)*(sp14) + (376579802636521/12500000000000 : ℝ)*(sp15) + (1506413768481177/50000000000000 : ℝ)*(f.failure) + (243786957618679/4000000000000 : ℝ)*(f.sum) + (5673144792799/13250000000000000000000000000 : ℝ)*base65 + (41953950884055619721/662500000000000000000000000000000 : ℝ)*base68 + (29305874013256880279/662500000000000000000000000000000 : ℝ)*base69 + (2455071003494380279/662500000000000000000000000000000 : ℝ)*base71 + (78152735532701/13250000000000000000000000000 : ℝ)*base74 + (1181678133019380279/662500000000000000000000000000000 : ℝ)*base75 + (7488515817869380279/662500000000000000000000000000000 : ℝ)*base77 + (25853497012819380279/662500000000000000000000000000000 : ℝ)*base79 + (29512580166201/13250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (43977/156250000000000000000 : ℝ)*base89 + (43977/156250000000000000000 : ℝ)*base91 + (43977/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1204_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(59347/100000 : ℝ) else (19999/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41631/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1204_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1204_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(59347/100000 : ℝ) else (19999/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41631/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1204_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(59347/100000 : ℝ) else (19999/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41631/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
