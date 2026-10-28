-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:00:24.21681+00:00
-- url     : https://prove2.me/submissions/3363788c-ba02-452a-86aa-c927e5a7d2c4

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
theorem support_rectangle_w1100_s0_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1905175107/10000000000 : ℝ)*x 0 + (758011071/1250000000 : ℝ)*x 1 + (477513753/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1905175107/10000000000 : ℝ)^8293 ≤ (11061016852573/100000000000000 : ℝ)^6245 := by
    have hnat : (1905175107 : ℕ)^8293*100000000000000^6245 ≤ 11061016852573^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905175107 10000000000 11061016852573 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758011071/1250000000 : ℝ)^8293 ≤ (25733280765791/50000000000000 : ℝ)^6245 := by
    have hnat : (758011071 : ℕ)^8293*50000000000000^6245 ≤ 25733280765791^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758011071 1250000000 25733280765791 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477513753/1000000000 : ℝ)^8293 ≤ (9368105399277/25000000000000 : ℝ)^6245 := by
    have hnat : (477513753 : ℕ)^8293*25000000000000^6245 ≤ 9368105399277^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477513753 1000000000 9368105399277 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1905175107/10000000000 : ℝ), (758011071/1250000000 : ℝ), (477513753/1000000000 : ℝ)] ![(11061016852573/100000000000000 : ℝ), (25733280765791/50000000000000 : ℝ), (9368105399277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1905175107/10000000000 : ℝ)|^8293 ≤ (11061016852573/100000000000000 : ℝ)^6245
        have hw : |(-1905175107/10000000000 : ℝ)|=(1905175107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(758011071/1250000000 : ℝ)|^8293 ≤ (25733280765791/50000000000000 : ℝ)^6245
        have hw : |(758011071/1250000000 : ℝ)|=(758011071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477513753/1000000000 : ℝ)|^8293 ≤ (9368105399277/25000000000000 : ℝ)^6245
        have hw : |(477513753/1000000000 : ℝ)|=(477513753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s0_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689894899/1250000000 : ℝ)*x 0 + (-661525627/2500000000 : ℝ)*x 1 + (477513753/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689894899/1250000000 : ℝ)^8293 ≤ (5677173042457/12500000000000 : ℝ)^6245 := by
    have hnat : (689894899 : ℕ)^8293*12500000000000^6245 ≤ 5677173042457^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689894899 1250000000 5677173042457 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (661525627/2500000000 : ℝ)^8293 ≤ (17110194043747/100000000000000 : ℝ)^6245 := by
    have hnat : (661525627 : ℕ)^8293*100000000000000^6245 ≤ 17110194043747^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661525627 2500000000 17110194043747 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477513753/1000000000 : ℝ)^8293 ≤ (9368105399277/25000000000000 : ℝ)^6245 := by
    have hnat : (477513753 : ℕ)^8293*25000000000000^6245 ≤ 9368105399277^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477513753 1000000000 9368105399277 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689894899/1250000000 : ℝ), (-661525627/2500000000 : ℝ), (477513753/1000000000 : ℝ)] ![(5677173042457/12500000000000 : ℝ), (17110194043747/100000000000000 : ℝ), (9368105399277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689894899/1250000000 : ℝ)|^8293 ≤ (5677173042457/12500000000000 : ℝ)^6245
        have hw : |(689894899/1250000000 : ℝ)|=(689894899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-661525627/2500000000 : ℝ)|^8293 ≤ (17110194043747/100000000000000 : ℝ)^6245
        have hw : |(-661525627/2500000000 : ℝ)|=(661525627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477513753/1000000000 : ℝ)|^8293 ≤ (9368105399277/25000000000000 : ℝ)^6245
        have hw : |(477513753/1000000000 : ℝ)|=(477513753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s0_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689894899/1250000000 : ℝ)*x 0 + (4775137531/10000000000 : ℝ)*x 1 + (-661525627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689894899/1250000000 : ℝ)^8293 ≤ (5677173042457/12500000000000 : ℝ)^6245 := by
    have hnat : (689894899 : ℕ)^8293*12500000000000^6245 ≤ 5677173042457^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689894899 1250000000 5677173042457 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4775137531/10000000000 : ℝ)^8293 ≤ (37472421607529/100000000000000 : ℝ)^6245 := by
    have hnat : (4775137531 : ℕ)^8293*100000000000000^6245 ≤ 37472421607529^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775137531 10000000000 37472421607529 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (661525627/2500000000 : ℝ)^8293 ≤ (17110194043747/100000000000000 : ℝ)^6245 := by
    have hnat : (661525627 : ℕ)^8293*100000000000000^6245 ≤ 17110194043747^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661525627 2500000000 17110194043747 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689894899/1250000000 : ℝ), (4775137531/10000000000 : ℝ), (-661525627/2500000000 : ℝ)] ![(5677173042457/12500000000000 : ℝ), (37472421607529/100000000000000 : ℝ), (17110194043747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689894899/1250000000 : ℝ)|^8293 ≤ (5677173042457/12500000000000 : ℝ)^6245
        have hw : |(689894899/1250000000 : ℝ)|=(689894899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4775137531/10000000000 : ℝ)|^8293 ≤ (37472421607529/100000000000000 : ℝ)^6245
        have hw : |(4775137531/10000000000 : ℝ)|=(4775137531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-661525627/2500000000 : ℝ)|^8293 ≤ (17110194043747/100000000000000 : ℝ)^6245
        have hw : |(-661525627/2500000000 : ℝ)|=(661525627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s0_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (840881887/2000000000 : ℝ)*x 0 + (1561552547/5000000000 : ℝ)*x 1 + (177072869/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840881887/2000000000 : ℝ)^8293 ≤ (3955596169101/12500000000000 : ℝ)^6245 := by
    have hnat : (840881887 : ℕ)^8293*12500000000000^6245 ≤ 3955596169101^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840881887 2000000000 3955596169101 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561552547/5000000000 : ℝ)^8293 ≤ (21322598935629/100000000000000 : ℝ)^6245 := by
    have hnat : (1561552547 : ℕ)^8293*100000000000000^6245 ≤ 21322598935629^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561552547 5000000000 21322598935629 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177072869/312500000 : ℝ)^8293 ≤ (940652633817/2000000000000 : ℝ)^6245 := by
    have hnat : (177072869 : ℕ)^8293*2000000000000^6245 ≤ 940652633817^6245*312500000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177072869 312500000 940652633817 2000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840881887/2000000000 : ℝ), (1561552547/5000000000 : ℝ), (177072869/312500000 : ℝ)] ![(3955596169101/12500000000000 : ℝ), (21322598935629/100000000000000 : ℝ), (940652633817/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840881887/2000000000 : ℝ)|^8293 ≤ (3955596169101/12500000000000 : ℝ)^6245
        have hw : |(840881887/2000000000 : ℝ)|=(840881887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561552547/5000000000 : ℝ)|^8293 ≤ (21322598935629/100000000000000 : ℝ)^6245
        have hw : |(1561552547/5000000000 : ℝ)|=(1561552547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(177072869/312500000 : ℝ)|^8293 ≤ (940652633817/2000000000000 : ℝ)^6245
        have hw : |(177072869/312500000 : ℝ)|=(177072869/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s0_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-955223189/5000000000 : ℝ)*x 0 + (1202101919/2500000000 : ℝ)*x 1 + (1205930273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955223189/5000000000 : ℝ)^8293 ≤ (2775418843609/25000000000000 : ℝ)^6245 := by
    have hnat : (955223189 : ℕ)^8293*25000000000000^6245 ≤ 2775418843609^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955223189 5000000000 2775418843609 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202101919/2500000000 : ℝ)^8293 ≤ (1890976091653/5000000000000 : ℝ)^6245 := by
    have hnat : (1202101919 : ℕ)^8293*5000000000000^6245 ≤ 1890976091653^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202101919 2500000000 1890976091653 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205930273/2000000000 : ℝ)^8293 ≤ (51078802783637/100000000000000 : ℝ)^6245 := by
    have hnat : (1205930273 : ℕ)^8293*100000000000000^6245 ≤ 51078802783637^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205930273 2000000000 51078802783637 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955223189/5000000000 : ℝ), (1202101919/2500000000 : ℝ), (1205930273/2000000000 : ℝ)] ![(2775418843609/25000000000000 : ℝ), (1890976091653/5000000000000 : ℝ), (51078802783637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955223189/5000000000 : ℝ)|^8293 ≤ (2775418843609/25000000000000 : ℝ)^6245
        have hw : |(-955223189/5000000000 : ℝ)|=(955223189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1202101919/2500000000 : ℝ)|^8293 ≤ (1890976091653/5000000000000 : ℝ)^6245
        have hw : |(1202101919/2500000000 : ℝ)|=(1202101919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205930273/2000000000 : ℝ)|^8293 ≤ (51078802783637/100000000000000 : ℝ)^6245
        have hw : |(1205930273/2000000000 : ℝ)|=(1205930273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s0_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1033827019/2000000000 : ℝ)*x 0 + (-1391590177/10000000000 : ℝ)*x 1 + (94213313/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033827019/2000000000 : ℝ)^8293 ≤ (41632785448449/100000000000000 : ℝ)^6245 := by
    have hnat : (1033827019 : ℕ)^8293*100000000000000^6245 ≤ 41632785448449^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033827019 2000000000 41632785448449 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391590177/10000000000 : ℝ)^8293 ≤ (72884042381/1000000000000 : ℝ)^6245 := by
    have hnat : (1391590177 : ℕ)^8293*1000000000000^6245 ≤ 72884042381^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391590177 10000000000 72884042381 1000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94213313/156250000 : ℝ)^8293 ≤ (51078810286959/100000000000000 : ℝ)^6245 := by
    have hnat : (94213313 : ℕ)^8293*100000000000000^6245 ≤ 51078810286959^6245*156250000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94213313 156250000 51078810286959 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033827019/2000000000 : ℝ), (-1391590177/10000000000 : ℝ), (94213313/156250000 : ℝ)] ![(41632785448449/100000000000000 : ℝ), (72884042381/1000000000000 : ℝ), (51078810286959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033827019/2000000000 : ℝ)|^8293 ≤ (41632785448449/100000000000000 : ℝ)^6245
        have hw : |(1033827019/2000000000 : ℝ)|=(1033827019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1391590177/10000000000 : ℝ)|^8293 ≤ (72884042381/1000000000000 : ℝ)^6245
        have hw : |(-1391590177/10000000000 : ℝ)|=(1391590177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94213313/156250000 : ℝ)|^8293 ≤ (51078810286959/100000000000000 : ℝ)^6245
        have hw : |(94213313/156250000 : ℝ)|=(94213313/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s0_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169136517/10000000000 : ℝ)*x 0 + (6029651781/10000000000 : ℝ)*x 1 + (-695794199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169136517/10000000000 : ℝ)^8293 ≤ (416328006573/1000000000000 : ℝ)^6245 := by
    have hnat : (5169136517 : ℕ)^8293*1000000000000^6245 ≤ 416328006573^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169136517 10000000000 416328006573 1000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6029651781/10000000000 : ℝ)^8293 ≤ (5107880746337/10000000000000 : ℝ)^6245 := by
    have hnat : (6029651781 : ℕ)^8293*10000000000000^6245 ≤ 5107880746337^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029651781 10000000000 5107880746337 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695794199/5000000000 : ℝ)^8293 ≤ (7288391865067/100000000000000 : ℝ)^6245 := by
    have hnat : (695794199 : ℕ)^8293*100000000000000^6245 ≤ 7288391865067^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695794199 5000000000 7288391865067 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169136517/10000000000 : ℝ), (6029651781/10000000000 : ℝ), (-695794199/5000000000 : ℝ)] ![(416328006573/1000000000000 : ℝ), (5107880746337/10000000000000 : ℝ), (7288391865067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169136517/10000000000 : ℝ)|^8293 ≤ (416328006573/1000000000000 : ℝ)^6245
        have hw : |(5169136517/10000000000 : ℝ)|=(5169136517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6029651781/10000000000 : ℝ)|^8293 ≤ (5107880746337/10000000000000 : ℝ)^6245
        have hw : |(6029651781/10000000000 : ℝ)|=(6029651781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-695794199/5000000000 : ℝ)|^8293 ≤ (7288391865067/100000000000000 : ℝ)^6245
        have hw : |(-695794199/5000000000 : ℝ)|=(695794199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s0_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4214807143/10000000000 : ℝ)*x 0 + (2800343701/5000000000 : ℝ)*x 1 + (1595525887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214807143/10000000000 : ℝ)^8293 ≤ (7937183743287/25000000000000 : ℝ)^6245 := by
    have hnat : (4214807143 : ℕ)^8293*25000000000000^6245 ≤ 7937183743287^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214807143 10000000000 7937183743287 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2800343701/5000000000 : ℝ)^8293 ≤ (23155225148247/50000000000000 : ℝ)^6245 := by
    have hnat : (2800343701 : ℕ)^8293*50000000000000^6245 ≤ 23155225148247^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800343701 5000000000 23155225148247 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595525887/5000000000 : ℝ)^8293 ≤ (2742601838799/12500000000000 : ℝ)^6245 := by
    have hnat : (1595525887 : ℕ)^8293*12500000000000^6245 ≤ 2742601838799^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595525887 5000000000 2742601838799 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214807143/10000000000 : ℝ), (2800343701/5000000000 : ℝ), (1595525887/5000000000 : ℝ)] ![(7937183743287/25000000000000 : ℝ), (23155225148247/50000000000000 : ℝ), (2742601838799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214807143/10000000000 : ℝ)|^8293 ≤ (7937183743287/25000000000000 : ℝ)^6245
        have hw : |(4214807143/10000000000 : ℝ)|=(4214807143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2800343701/5000000000 : ℝ)|^8293 ≤ (23155225148247/50000000000000 : ℝ)^6245
        have hw : |(2800343701/5000000000 : ℝ)|=(2800343701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595525887/5000000000 : ℝ)|^8293 ≤ (2742601838799/12500000000000 : ℝ)^6245
        have hw : |(1595525887/5000000000 : ℝ)|=(1595525887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (239/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27977/100000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (2073/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2073 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2073*1^512 ≤ 0^512*1^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2073/512 : ℝ) ≤ (1223994045804179103/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2073 ≤ (1223994045804179103/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2073*50000000000000000000^512 ≤ 1223994045804179103^512*5^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1223994045804179103 50000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1223994045804179103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2073 := by
      have hnat : (1 : ℕ)^512*1^2073 ≤ 1^2073*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51223994045804179103/50000000000000000000 : ℝ) ≤ (10059912218240109/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (51223994045804179103/50000000000000000000 : ℝ)^512 ≤ (10059912218240109/10000000000000000 : ℝ)^2073 := by
      have hnat : (51223994045804179103 : ℕ)^512*10000000000000000^2073 ≤ 10059912218240109^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51223994045804179103 50000000000000000000 10059912218240109 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059912218240109/10000000000000000 : ℝ)) (X := (51223994045804179103/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26223994045804179103/25000000000000000000 : ℝ) ≤ (5059912218240109/5000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (26223994045804179103/25000000000000000000 : ℝ)^512 ≤ (5059912218240109/5000000000000000 : ℝ)^2073 := by
      have hnat : (26223994045804179103 : ℕ)^512*5000000000000000^2073 ≤ 5059912218240109^2073*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26223994045804179103 25000000000000000000 5059912218240109 5000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059912218240109/5000000000000000 : ℝ)) (X := (26223994045804179103/25000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59912218240109/4000000000000000 : ℝ)*(0 : ℝ))^(2073/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59912218240109/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1223994045804179103/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59912218240109/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (1 : ℝ)+(59912218240109/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059912218240109/10000000000000000 : ℝ) by norm_num, show 1+(1223994045804179103/50000000000000000000 : ℝ)+(0 : ℝ)=(51223994045804179103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1223994045804179103/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59912218240109/4000000000000000 : ℝ)*(2/5 : ℝ))^(2073/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59912218240109/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059912218240109/5000000000000000 : ℝ) by norm_num, show 1+2*(1223994045804179103/50000000000000000000 : ℝ)=(26223994045804179103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59912218240109/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59912218240109/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59912218240109/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59912218240109/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59912218240109/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59912218240109/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1905175107/10000000000 : ℝ)*X 0 0+(758011071/1250000000 : ℝ)*X 0 1+(477513753/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689894899/1250000000 : ℝ)*X 1 0+(-661525627/2500000000 : ℝ)*X 1 1+(477513753/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689894899/1250000000 : ℝ)*X 2 0+(4775137531/10000000000 : ℝ)*X 2 1+(-661525627/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840881887/2000000000 : ℝ)*X 0 0+(1561552547/5000000000 : ℝ)*X 0 1+(177072869/312500000 : ℝ)*X 0 2+(840881887/2000000000 : ℝ)*X 1 0+(1561552547/5000000000 : ℝ)*X 1 1+(177072869/312500000 : ℝ)*X 1 2+(840881887/2000000000 : ℝ)*X 2 0+(1561552547/5000000000 : ℝ)*X 2 1+(177072869/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-955223189/5000000000 : ℝ)*X 0 0+(1202101919/2500000000 : ℝ)*X 0 1+(1205930273/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1033827019/2000000000 : ℝ)*X 1 0+(-1391590177/10000000000 : ℝ)*X 1 1+(94213313/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169136517/10000000000 : ℝ)*X 2 0+(6029651781/10000000000 : ℝ)*X 2 1+(-695794199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4214807143/10000000000 : ℝ)*X 0 0+(2800343701/5000000000 : ℝ)*X 0 1+(1595525887/5000000000 : ℝ)*X 0 2+(4214807143/10000000000 : ℝ)*X 1 0+(2800343701/5000000000 : ℝ)*X 1 1+(1595525887/5000000000 : ℝ)*X 1 2+(4214807143/10000000000 : ℝ)*X 2 0+(2800343701/5000000000 : ℝ)*X 2 1+(1595525887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1328085562752610212618669/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70908351/100000000000000 : ℝ)*(base1) + (25882311/1562500000000 : ℝ)*(base19) + (1543797071/100000000000000 : ℝ)*(base23) + (7041927/6250000000000 : ℝ)*(base24) + (46930017/12500000000000 : ℝ)*(upper3) + (584519954817351/100000000000000 : ℝ)*(major0) + (584519954817351/100000000000000 : ℝ)*(major1) + (584519954817351/100000000000000 : ℝ)*(major2) + (9697876798893/1250000000000 : ℝ)*(sp0) + (77583205285897/10000000000000 : ℝ)*(sp1) + (77583205285897/10000000000000 : ℝ)*(sp2) + (1228759378803/312500000000 : ℝ)*(sp3) + (454540473/12500000000000 : ℝ)*(sp4) + (2906834919/100000000000000 : ℝ)*(sp7) + (39320597896023/10000000000000 : ℝ)*(f.failure) + (387916854663437/50000000000000 : ℝ)*(f.sum) + (235032640331259/200000000000000000000000000000 : ℝ)*base65 + (1374098324531259/400000000000000000000000000000 : ℝ)*base67 + (2155098418931259/400000000000000000000000000000 : ℝ)*base69 + (831447254531259/400000000000000000000000000000 : ℝ)*base71 + (300148173731259/200000000000000000000000000000 : ℝ)*base73 + (55395877068741/400000000000000000000000000000 : ℝ)*base76 + (831447254531259/400000000000000000000000000000 : ℝ)*base77 + (1381450658131259/400000000000000000000000000000 : ℝ)*base79 + (28846887868741/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5373/10000000000000000000 : ℝ)*base90 + (5373/10000000000000000000 : ℝ)*base92 + (5373/10000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1124005216067998014267867/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (762518947/100000000000000 : ℝ)*(base19) + (1448502753/100000000000000 : ℝ)*(base23) + (217821357/50000000000000 : ℝ)*(base39) + (30247317/12500000000000 : ℝ)*(base45) + (28846051/25000000000000 : ℝ)*(upper3) + (303888999/100000000000000 : ℝ)*(upper5) + (616916570789483/100000000000000 : ℝ)*(major0) + (616916570789483/100000000000000 : ℝ)*(major1) + (616916135146769/100000000000000 : ℝ)*(major2) + (55687283/10000000000000 : ℝ)*(sp2) + (818833369035173/100000000000000 : ℝ)*(sp4) + (409416303258113/50000000000000 : ℝ)*(sp5) + (25588493728197/3125000000000 : ℝ)*(sp6) + (51874893695859/12500000000000 : ℝ)*(sp7) + (51874893695859/12500000000000 : ℝ)*(f.failure) + (818833804677887/100000000000000 : ℝ)*(f.sum) + (144652184317133/100000000000000000000000000000 : ℝ)*base66 + (3931036199242179/400000000000000000000000000000 : ℝ)*base68 + (2422622156773647/400000000000000000000000000000 : ℝ)*base69 + (983509668842179/400000000000000000000000000000 : ℝ)*base72 + (507144308317133/100000000000000000000000000000 : ℝ)*base74 + (1149141878026353/400000000000000000000000000000 : ℝ)*base76 + (1105483103626353/400000000000000000000000000000 : ℝ)*base78 + (907554093226353/400000000000000000000000000000 : ℝ)*base80 + (81278126773647/200000000000000000000000000000 : ℝ)*base81 + (125591/12500000000000000000 : ℝ)*base89 + (125591/12500000000000000000 : ℝ)*base91 + (125591/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1100_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27977/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1100_s1_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112868137/10000000000 : ℝ)*x 0 + (571288991/1000000000 : ℝ)*x 1 + (1248337681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112868137/10000000000 : ℝ)^8293 ≤ (101521831599/800000000000 : ℝ)^6245 := by
    have hnat : (2112868137 : ℕ)^8293*800000000000^6245 ≤ 101521831599^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112868137 10000000000 101521831599 800000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571288991/1000000000 : ℝ)^8293 ≤ (5943313030599/12500000000000 : ℝ)^6245 := by
    have hnat : (571288991 : ℕ)^8293*12500000000000^6245 ≤ 5943313030599^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571288991 1000000000 5943313030599 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248337681/2500000000 : ℝ)^8293 ≤ (7952653357831/20000000000000 : ℝ)^6245 := by
    have hnat : (1248337681 : ℕ)^8293*20000000000000^6245 ≤ 7952653357831^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248337681 2500000000 7952653357831 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112868137/10000000000 : ℝ), (571288991/1000000000 : ℝ), (1248337681/2500000000 : ℝ)] ![(101521831599/800000000000 : ℝ), (5943313030599/12500000000000 : ℝ), (7952653357831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112868137/10000000000 : ℝ)|^8293 ≤ (101521831599/800000000000 : ℝ)^6245
        have hw : |(-2112868137/10000000000 : ℝ)|=(2112868137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571288991/1000000000 : ℝ)|^8293 ≤ (5943313030599/12500000000000 : ℝ)^6245
        have hw : |(571288991/1000000000 : ℝ)|=(571288991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248337681/2500000000 : ℝ)|^8293 ≤ (7952653357831/20000000000000 : ℝ)^6245
        have hw : |(1248337681/2500000000 : ℝ)|=(1248337681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s1_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5421435209/10000000000 : ℝ)*x 0 + (-100080567/400000000 : ℝ)*x 1 + (2496675421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421435209/10000000000 : ℝ)^8293 ≤ (44352599658379/100000000000000 : ℝ)^6245 := by
    have hnat : (5421435209 : ℕ)^8293*100000000000000^6245 ≤ 44352599658379^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421435209 10000000000 44352599658379 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100080567/400000000 : ℝ)^8293 ≤ (15884132285677/100000000000000 : ℝ)^6245 := by
    have hnat : (100080567 : ℕ)^8293*100000000000000^6245 ≤ 15884132285677^6245*400000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100080567 400000000 15884132285677 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2496675421/5000000000 : ℝ)^8293 ≤ (39763268036973/100000000000000 : ℝ)^6245 := by
    have hnat : (2496675421 : ℕ)^8293*100000000000000^6245 ≤ 39763268036973^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496675421 5000000000 39763268036973 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421435209/10000000000 : ℝ), (-100080567/400000000 : ℝ), (2496675421/5000000000 : ℝ)] ![(44352599658379/100000000000000 : ℝ), (15884132285677/100000000000000 : ℝ), (39763268036973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421435209/10000000000 : ℝ)|^8293 ≤ (44352599658379/100000000000000 : ℝ)^6245
        have hw : |(5421435209/10000000000 : ℝ)|=(5421435209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100080567/400000000 : ℝ)|^8293 ≤ (15884132285677/100000000000000 : ℝ)^6245
        have hw : |(-100080567/400000000 : ℝ)|=(100080567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2496675421/5000000000 : ℝ)|^8293 ≤ (39763268036973/100000000000000 : ℝ)^6245
        have hw : |(2496675421/5000000000 : ℝ)|=(2496675421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s1_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42354971/78125000 : ℝ)*x 0 + (4993349781/10000000000 : ℝ)*x 1 + (-625503529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42354971/78125000 : ℝ)^8293 ≤ (44352611380481/100000000000000 : ℝ)^6245 := by
    have hnat : (42354971 : ℕ)^8293*100000000000000^6245 ≤ 44352611380481^6245*78125000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42354971 78125000 44352611380481 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993349781/10000000000 : ℝ)^8293 ≤ (39763256817187/100000000000000 : ℝ)^6245 := by
    have hnat : (4993349781 : ℕ)^8293*100000000000000^6245 ≤ 39763256817187^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993349781 10000000000 39763256817187 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625503529/2500000000 : ℝ)^8293 ≤ (7942065894139/50000000000000 : ℝ)^6245 := by
    have hnat : (625503529 : ℕ)^8293*50000000000000^6245 ≤ 7942065894139^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625503529 2500000000 7942065894139 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42354971/78125000 : ℝ), (4993349781/10000000000 : ℝ), (-625503529/2500000000 : ℝ)] ![(44352611380481/100000000000000 : ℝ), (39763256817187/100000000000000 : ℝ), (7942065894139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42354971/78125000 : ℝ)|^8293 ≤ (44352611380481/100000000000000 : ℝ)^6245
        have hw : |(42354971/78125000 : ℝ)|=(42354971/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993349781/10000000000 : ℝ)|^8293 ≤ (39763256817187/100000000000000 : ℝ)^6245
        have hw : |(4993349781/10000000000 : ℝ)|=(4993349781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-625503529/2500000000 : ℝ)|^8293 ≤ (7942065894139/50000000000000 : ℝ)^6245
        have hw : |(-625503529/2500000000 : ℝ)|=(625503529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s1_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4320972301/10000000000 : ℝ)*x 0 + (733814663/2000000000 : ℝ)*x 1 + (5088793113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320972301/10000000000 : ℝ)^8293 ≤ (3281506099611/10000000000000 : ℝ)^6245 := by
    have hnat : (4320972301 : ℕ)^8293*10000000000000^6245 ≤ 3281506099611^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320972301 10000000000 3281506099611 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733814663/2000000000 : ℝ)^8293 ≤ (26409245109807/100000000000000 : ℝ)^6245 := by
    have hnat : (733814663 : ℕ)^8293*100000000000000^6245 ≤ 26409245109807^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733814663 2000000000 26409245109807 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5088793113/10000000000 : ℝ)^8293 ≤ (10193923466719/25000000000000 : ℝ)^6245 := by
    have hnat : (5088793113 : ℕ)^8293*25000000000000^6245 ≤ 10193923466719^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088793113 10000000000 10193923466719 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320972301/10000000000 : ℝ), (733814663/2000000000 : ℝ), (5088793113/10000000000 : ℝ)] ![(3281506099611/10000000000000 : ℝ), (26409245109807/100000000000000 : ℝ), (10193923466719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320972301/10000000000 : ℝ)|^8293 ≤ (3281506099611/10000000000000 : ℝ)^6245
        have hw : |(4320972301/10000000000 : ℝ)|=(4320972301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733814663/2000000000 : ℝ)|^8293 ≤ (26409245109807/100000000000000 : ℝ)^6245
        have hw : |(733814663/2000000000 : ℝ)|=(733814663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5088793113/10000000000 : ℝ)|^8293 ≤ (10193923466719/25000000000000 : ℝ)^6245
        have hw : |(5088793113/10000000000 : ℝ)|=(5088793113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s1_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-422746957/2000000000 : ℝ)*x 0 + (500333429/1000000000 : ℝ)*x 1 + (5702705923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422746957/2000000000 : ℝ)^8293 ≤ (198392838409/1562500000000 : ℝ)^6245 := by
    have hnat : (422746957 : ℕ)^8293*1562500000000^6245 ≤ 198392838409^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422746957 2000000000 198392838409 1562500000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500333429/1000000000 : ℝ)^8293 ≤ (19934437440251/50000000000000 : ℝ)^6245 := by
    have hnat : (500333429 : ℕ)^8293*50000000000000^6245 ≤ 19934437440251^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500333429 1000000000 19934437440251 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5702705923/10000000000 : ℝ)^8293 ≤ (9486796690477/20000000000000 : ℝ)^6245 := by
    have hnat : (5702705923 : ℕ)^8293*20000000000000^6245 ≤ 9486796690477^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5702705923 10000000000 9486796690477 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422746957/2000000000 : ℝ), (500333429/1000000000 : ℝ), (5702705923/10000000000 : ℝ)] ![(198392838409/1562500000000 : ℝ), (19934437440251/50000000000000 : ℝ), (9486796690477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422746957/2000000000 : ℝ)|^8293 ≤ (198392838409/1562500000000 : ℝ)^6245
        have hw : |(-422746957/2000000000 : ℝ)|=(422746957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500333429/1000000000 : ℝ)|^8293 ≤ (19934437440251/50000000000000 : ℝ)^6245
        have hw : |(500333429/1000000000 : ℝ)|=(500333429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5702705923/10000000000 : ℝ)|^8293 ≤ (9486796690477/20000000000000 : ℝ)^6245
        have hw : |(5702705923/10000000000 : ℝ)|=(5702705923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s1_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (209494049/400000000 : ℝ)*x 0 + (-179265879/1000000000 : ℝ)*x 1 + (22810823/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209494049/400000000 : ℝ)^8293 ≤ (1694558320203/4000000000000 : ℝ)^6245 := by
    have hnat : (209494049 : ℕ)^8293*4000000000000^6245 ≤ 1694558320203^6245*400000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209494049 400000000 1694558320203 4000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179265879/1000000000 : ℝ)^8293 ≤ (637628777623/6250000000000 : ℝ)^6245 := by
    have hnat : (179265879 : ℕ)^8293*6250000000000^6245 ≤ 637628777623^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179265879 1000000000 637628777623 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22810823/40000000 : ℝ)^8293 ≤ (47433981541503/100000000000000 : ℝ)^6245 := by
    have hnat : (22810823 : ℕ)^8293*100000000000000^6245 ≤ 47433981541503^6245*40000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22810823 40000000 47433981541503 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209494049/400000000 : ℝ), (-179265879/1000000000 : ℝ), (22810823/40000000 : ℝ)] ![(1694558320203/4000000000000 : ℝ), (637628777623/6250000000000 : ℝ), (47433981541503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209494049/400000000 : ℝ)|^8293 ≤ (1694558320203/4000000000000 : ℝ)^6245
        have hw : |(209494049/400000000 : ℝ)|=(209494049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179265879/1000000000 : ℝ)|^8293 ≤ (637628777623/6250000000000 : ℝ)^6245
        have hw : |(-179265879/1000000000 : ℝ)|=(179265879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22810823/40000000 : ℝ)|^8293 ≤ (47433981541503/100000000000000 : ℝ)^6245
        have hw : |(22810823/40000000 : ℝ)|=(22810823/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s1_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237351247/10000000000 : ℝ)*x 0 + (142567647/250000000 : ℝ)*x 1 + (-224082321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237351247/10000000000 : ℝ)^8293 ≤ (10590989560347/25000000000000 : ℝ)^6245 := by
    have hnat : (5237351247 : ℕ)^8293*25000000000000^6245 ≤ 10590989560347^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237351247 10000000000 10590989560347 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142567647/250000000 : ℝ)^8293 ≤ (23716991488713/50000000000000 : ℝ)^6245 := by
    have hnat : (142567647 : ℕ)^8293*50000000000000^6245 ≤ 23716991488713^6245*250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142567647 250000000 23716991488713 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224082321/1250000000 : ℝ)^8293 ≤ (10202058764237/100000000000000 : ℝ)^6245 := by
    have hnat : (224082321 : ℕ)^8293*100000000000000^6245 ≤ 10202058764237^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224082321 1250000000 10202058764237 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237351247/10000000000 : ℝ), (142567647/250000000 : ℝ), (-224082321/1250000000 : ℝ)] ![(10590989560347/25000000000000 : ℝ), (23716991488713/50000000000000 : ℝ), (10202058764237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237351247/10000000000 : ℝ)|^8293 ≤ (10590989560347/25000000000000 : ℝ)^6245
        have hw : |(5237351247/10000000000 : ℝ)|=(5237351247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142567647/250000000 : ℝ)|^8293 ≤ (23716991488713/50000000000000 : ℝ)^6245
        have hw : |(142567647/250000000 : ℝ)|=(142567647/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224082321/1250000000 : ℝ)|^8293 ≤ (10202058764237/100000000000000 : ℝ)^6245
        have hw : |(-224082321/1250000000 : ℝ)|=(224082321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s1_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (864536229/2000000000 : ℝ)*x 0 + (506909531/1000000000 : ℝ)*x 1 + (3689166543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864536229/2000000000 : ℝ)^8293 ≤ (32832295609007/100000000000000 : ℝ)^6245 := by
    have hnat : (864536229 : ℕ)^8293*100000000000000^6245 ≤ 32832295609007^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864536229 2000000000 32832295609007 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506909531/1000000000 : ℝ)^8293 ≤ (20283115365149/50000000000000 : ℝ)^6245 := by
    have hnat : (506909531 : ℕ)^8293*50000000000000^6245 ≤ 20283115365149^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506909531 1000000000 20283115365149 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3689166543/10000000000 : ℝ)^8293 ≤ (26601473647869/100000000000000 : ℝ)^6245 := by
    have hnat : (3689166543 : ℕ)^8293*100000000000000^6245 ≤ 26601473647869^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689166543 10000000000 26601473647869 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864536229/2000000000 : ℝ), (506909531/1000000000 : ℝ), (3689166543/10000000000 : ℝ)] ![(32832295609007/100000000000000 : ℝ), (20283115365149/50000000000000 : ℝ), (26601473647869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864536229/2000000000 : ℝ)|^8293 ≤ (32832295609007/100000000000000 : ℝ)^6245
        have hw : |(864536229/2000000000 : ℝ)|=(864536229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506909531/1000000000 : ℝ)|^8293 ≤ (20283115365149/50000000000000 : ℝ)^6245
        have hw : |(506909531/1000000000 : ℝ)|=(506909531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3689166543/10000000000 : ℝ)|^8293 ≤ (26601473647869/100000000000000 : ℝ)^6245
        have hw : |(3689166543/10000000000 : ℝ)|=(3689166543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5411/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2063/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (239/100000 : ℝ) ^ (2073/512 : ℝ) ≤ (485974727/20000000000000000000 : ℝ) := by
    have hpowers : (239/100000 : ℝ)^2073 ≤ (485974727/20000000000000000000 : ℝ)^512 := by
      have hnat : (239 : ℕ)^2073*20000000000000000000^512 ≤ 485974727^512*100000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        239 100000 485974727 20000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (239/100000 : ℝ)) (X := (485974727/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27977/100000 : ℝ) ^ (2073/512 : ℝ) ≤ (575695597686937661/100000000000000000000 : ℝ) := by
    have hpowers : (27977/100000 : ℝ)^2073 ≤ (575695597686937661/100000000000000000000 : ℝ)^512 := by
      have hnat : (27977 : ℕ)^2073*100000000000000000000^512 ≤ 575695597686937661^512*100000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27977 100000 575695597686937661 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27977/100000 : ℝ)) (X := (575695597686937661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000000485974727/10000000000000000000 : ℝ) ≤ (10000000000120029/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (10000000000485974727/10000000000000000000 : ℝ)^512 ≤ (10000000000120029/10000000000000000 : ℝ)^2073 := by
      have hnat : (10000000000485974727 : ℕ)^512*10000000000000000^2073 ≤ 10000000000120029^2073*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000000485974727 10000000000000000000 10000000000120029 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000120029/10000000000000000 : ℝ)) (X := (10000000000485974727/10000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3142990487503650353/3125000000000000000 : ℝ) ≤ (2503547025966957/2500000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (3142990487503650353/3125000000000000000 : ℝ)^512 ≤ (2503547025966957/2500000000000000 : ℝ)^2073 := by
      have hnat : (3142990487503650353 : ℕ)^512*2500000000000000^2073 ≤ 2503547025966957^2073*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3142990487503650353 3125000000000000000 2503547025966957 2500000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503547025966957/2500000000000000 : ℝ)) (X := (3142990487503650353/3125000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50575695597686937661/50000000000000000000 : ℝ) ≤ (10028376207615627/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50575695597686937661/50000000000000000000 : ℝ)^512 ≤ (10028376207615627/10000000000000000 : ℝ)^2073 := by
      have hnat : (50575695597686937661 : ℕ)^512*10000000000000000^2073 ≤ 10028376207615627^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50575695597686937661 50000000000000000000 10028376207615627 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028376207615627/10000000000000000 : ℝ)) (X := (50575695597686937661/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(485974727/20000000000000000000 : ℝ) ≤ ((288930435510143663/288937500000000000 : ℝ)+2*(4729367915933/924600000000000 : ℝ)*(239/100000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (288930435510143663/288937500000000000 : ℝ)+2*(4729367915933/924600000000000 : ℝ)*(239/100000 : ℝ)=(10000000000120029/10000000000000000 : ℝ) by norm_num, show 1+2*(485974727/20000000000000000000 : ℝ)=(10000000000485974727/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(575695597686937661/100000000000000000000 : ℝ)+(485974727/20000000000000000000 : ℝ) ≤ ((288930435510143663/288937500000000000 : ℝ)+(4729367915933/924600000000000 : ℝ)*((27977/100000 : ℝ)+(239/100000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (288930435510143663/288937500000000000 : ℝ)+(4729367915933/924600000000000 : ℝ)*((27977/100000 : ℝ)+(239/100000 : ℝ))=(2503547025966957/2500000000000000 : ℝ) by norm_num, show 1+(575695597686937661/100000000000000000000 : ℝ)+(485974727/20000000000000000000 : ℝ)=(3142990487503650353/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(575695597686937661/100000000000000000000 : ℝ) ≤ ((288930435510143663/288937500000000000 : ℝ)+2*(4729367915933/924600000000000 : ℝ)*(27977/100000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (288930435510143663/288937500000000000 : ℝ)+2*(4729367915933/924600000000000 : ℝ)*(27977/100000 : ℝ)=(10028376207615627/10000000000000000 : ℝ) by norm_num, show 1+2*(575695597686937661/100000000000000000000 : ℝ)=(50575695597686937661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (288930435510143663/288937500000000000 : ℝ)*(X 1 0+X 2 0)+(4729367915933/924600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (239/100000 : ℝ)) (hi := (27977/100000 : ℝ)) (c := (288930435510143663/288937500000000000 : ℝ)) (alpha := (4729367915933/924600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (288930435510143663/288937500000000000 : ℝ)*(X 0 1+X 2 1)+(4729367915933/924600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (239/100000 : ℝ)) (hi := (27977/100000 : ℝ)) (c := (288930435510143663/288937500000000000 : ℝ)) (alpha := (4729367915933/924600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (288930435510143663/288937500000000000 : ℝ)*(X 0 2+X 1 2)+(4729367915933/924600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (239/100000 : ℝ)) (hi := (27977/100000 : ℝ)) (c := (288930435510143663/288937500000000000 : ℝ)) (alpha := (4729367915933/924600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2112868137/10000000000 : ℝ)*X 0 0+(571288991/1000000000 : ℝ)*X 0 1+(1248337681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421435209/10000000000 : ℝ)*X 1 0+(-100080567/400000000 : ℝ)*X 1 1+(2496675421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42354971/78125000 : ℝ)*X 2 0+(4993349781/10000000000 : ℝ)*X 2 1+(-625503529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320972301/10000000000 : ℝ)*X 0 0+(733814663/2000000000 : ℝ)*X 0 1+(5088793113/10000000000 : ℝ)*X 0 2+(4320972301/10000000000 : ℝ)*X 1 0+(733814663/2000000000 : ℝ)*X 1 1+(5088793113/10000000000 : ℝ)*X 1 2+(4320972301/10000000000 : ℝ)*X 2 0+(733814663/2000000000 : ℝ)*X 2 1+(5088793113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-422746957/2000000000 : ℝ)*X 0 0+(500333429/1000000000 : ℝ)*X 0 1+(5702705923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((209494049/400000000 : ℝ)*X 1 0+(-179265879/1000000000 : ℝ)*X 1 1+(22810823/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5237351247/10000000000 : ℝ)*X 2 0+(142567647/250000000 : ℝ)*X 2 1+(-224082321/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864536229/2000000000 : ℝ)*X 0 0+(506909531/1000000000 : ℝ)*X 0 1+(3689166543/10000000000 : ℝ)*X 0 2+(864536229/2000000000 : ℝ)*X 1 0+(506909531/1000000000 : ℝ)*X 1 1+(3689166543/10000000000 : ℝ)*X 1 2+(864536229/2000000000 : ℝ)*X 2 0+(506909531/1000000000 : ℝ)*X 2 1+(3689166543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (330095645940205533275749/60195312500000000000000000000 : ℝ) := by norm_num
    linear_combination (190234699/100000000000000 : ℝ)*(base1) + (1030995403/100000000000000 : ℝ)*(base19) + (1307597271/100000000000000 : ℝ)*(base23) + (56994019/100000000000000 : ℝ)*(upper3) + (19001443/12500000000000 : ℝ)*(upper5) + (104707785476059/10000000000000 : ℝ)*(major0) + (104707785476059/10000000000000 : ℝ)*(major1) + (104707785476059/10000000000000 : ℝ)*(major2) + (694891071938669/50000000000000 : ℝ)*(sp0) + (694893144026459/50000000000000 : ℝ)*(sp1) + (27795720229021/2000000000000 : ℝ)*(sp2) + (8804577700387/1250000000000 : ℝ)*(sp3) + (2682702841/50000000000000 : ℝ)*(sp4) + (1801415749/100000000000000 : ℝ)*(sp7) + (5502876622511/781250000000 : ℝ)*(f.failure) + (1389787319048321/100000000000000 : ℝ)*(f.sum) + (24542971223/11557500000000000000000000 : ℝ)*base65 + (1650550287718297/1926250000000000000000000000000 : ℝ)*base68 + (10680707108137047/1926250000000000000000000000000 : ℝ)*base70 + (241144901539547/1926250000000000000000000000000 : ℝ)*base72 + (4595079814427/4623000000000000000000000000 : ℝ)*base73 + (3328697720515453/1926250000000000000000000000000 : ℝ)*base75 + (829253177862047/1926250000000000000000000000000 : ℝ)*base78 + (11909431653169203/1926250000000000000000000000000 : ℝ)*base79 + (8714643603527/2311500000000000000000000000 : ℝ)*base82 + (1209/195312500000000000 : ℝ)*base90 + (1209/195312500000000000 : ℝ)*base92 + (1209/195312500000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9344018596188979312185807/4815625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27334451/100000000000000 : ℝ)*(base1) + (228026163/50000000000000 : ℝ)*(base19) + (477581111/100000000000000 : ℝ)*(base23) + (19642593/50000000000000 : ℝ)*(upper3) + (20190141/50000000000000 : ℝ)*(upper5) + (269316275394609/25000000000000 : ℝ)*(major0) + (269316275394609/25000000000000 : ℝ)*(major1) + (269316275394609/25000000000000 : ℝ)*(major2) + (410124009/25000000000000 : ℝ)*(sp1) + (260264259/12500000000000 : ℝ)*(sp2) + (1429855027907239/100000000000000 : ℝ)*(sp4) + (714926452012213/50000000000000 : ℝ)*(sp5) + (285970488175521/20000000000000 : ℝ)*(sp6) + (724675110571151/100000000000000 : ℝ)*(sp7) + (724675137905603/100000000000000 : ℝ)*(f.failure) + (357463750143197/25000000000000 : ℝ)*(f.sum) + (1258050642199/3852500000000000000000000000 : ℝ)*base65 + (36350118825974553/4815625000000000000000000000000 : ℝ)*base67 + (40358883593880803/4815625000000000000000000000000 : ℝ)*base69 + (2545654656799107/1203906250000000000000000000000 : ℝ)*base71 + (9436904208237/1926250000000000000000000000 : ℝ)*base73 + (5331156653338393/1203906250000000000000000000000 : ℝ)*base76 + (13644981745393303/4815625000000000000000000000000 : ℝ)*base77 + (11825924943406697/4815625000000000000000000000000 : ℝ)*base80 + (27169391274093/7705000000000000000000000000 : ℝ)*base81 + (234047/100000000000000000000 : ℝ)*base89 + (234047/100000000000000000000 : ℝ)*base91 + (234047/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1100_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5411/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2063/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1100_s2_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542098097/2500000000 : ℝ)*x 0 + (5518986669/10000000000 : ℝ)*x 1 + (1287997751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542098097/2500000000 : ℝ)^8293 ≤ (13134978486787/100000000000000 : ℝ)^6245 := by
    have hnat : (542098097 : ℕ)^8293*100000000000000^6245 ≤ 13134978486787^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542098097 2500000000 13134978486787 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518986669/10000000000 : ℝ)^8293 ≤ (45415499071221/100000000000000 : ℝ)^6245 := by
    have hnat : (5518986669 : ℕ)^8293*100000000000000^6245 ≤ 45415499071221^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518986669 10000000000 45415499071221 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287997751/2500000000 : ℝ)^8293 ≤ (41449522424327/100000000000000 : ℝ)^6245 := by
    have hnat : (1287997751 : ℕ)^8293*100000000000000^6245 ≤ 41449522424327^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287997751 2500000000 41449522424327 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542098097/2500000000 : ℝ), (5518986669/10000000000 : ℝ), (1287997751/2500000000 : ℝ)] ![(13134978486787/100000000000000 : ℝ), (45415499071221/100000000000000 : ℝ), (41449522424327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542098097/2500000000 : ℝ)|^8293 ≤ (13134978486787/100000000000000 : ℝ)^6245
        have hw : |(-542098097/2500000000 : ℝ)|=(542098097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518986669/10000000000 : ℝ)|^8293 ≤ (45415499071221/100000000000000 : ℝ)^6245
        have hw : |(5518986669/10000000000 : ℝ)|=(5518986669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287997751/2500000000 : ℝ)|^8293 ≤ (41449522424327/100000000000000 : ℝ)^6245
        have hw : |(1287997751/2500000000 : ℝ)|=(1287997751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s2_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075137871/2000000000 : ℝ)*x 0 + (-2359514249/10000000000 : ℝ)*x 1 + (1030398423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075137871/2000000000 : ℝ)^8293 ≤ (21928156082431/50000000000000 : ℝ)^6245 := by
    have hnat : (1075137871 : ℕ)^8293*50000000000000^6245 ≤ 21928156082431^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075137871 2000000000 21928156082431 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2359514249/10000000000 : ℝ)^8293 ≤ (14694153521343/100000000000000 : ℝ)^6245 := by
    have hnat : (2359514249 : ℕ)^8293*100000000000000^6245 ≤ 14694153521343^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359514249 10000000000 14694153521343 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030398423/2000000000 : ℝ)^8293 ≤ (10362383573493/25000000000000 : ℝ)^6245 := by
    have hnat : (1030398423 : ℕ)^8293*25000000000000^6245 ≤ 10362383573493^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030398423 2000000000 10362383573493 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075137871/2000000000 : ℝ), (-2359514249/10000000000 : ℝ), (1030398423/2000000000 : ℝ)] ![(21928156082431/50000000000000 : ℝ), (14694153521343/100000000000000 : ℝ), (10362383573493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075137871/2000000000 : ℝ)|^8293 ≤ (21928156082431/50000000000000 : ℝ)^6245
        have hw : |(1075137871/2000000000 : ℝ)|=(1075137871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2359514249/10000000000 : ℝ)|^8293 ≤ (14694153521343/100000000000000 : ℝ)^6245
        have hw : |(-2359514249/10000000000 : ℝ)|=(2359514249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030398423/2000000000 : ℝ)|^8293 ≤ (10362383573493/25000000000000 : ℝ)^6245
        have hw : |(1030398423/2000000000 : ℝ)|=(1030398423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s2_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537568931/1000000000 : ℝ)*x 0 + (1030398433/2000000000 : ℝ)*x 1 + (-589878561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537568931/1000000000 : ℝ)^8293 ≤ (8771262335469/20000000000000 : ℝ)^6245 := by
    have hnat : (537568931 : ℕ)^8293*20000000000000^6245 ≤ 8771262335469^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537568931 1000000000 8771262335469 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030398433/2000000000 : ℝ)^8293 ≤ (41449534828159/100000000000000 : ℝ)^6245 := by
    have hnat : (1030398433 : ℕ)^8293*100000000000000^6245 ≤ 41449534828159^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030398433 2000000000 41449534828159 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589878561/2500000000 : ℝ)^8293 ≤ (14694153479993/100000000000000 : ℝ)^6245 := by
    have hnat : (589878561 : ℕ)^8293*100000000000000^6245 ≤ 14694153479993^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589878561 2500000000 14694153479993 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537568931/1000000000 : ℝ), (1030398433/2000000000 : ℝ), (-589878561/2500000000 : ℝ)] ![(8771262335469/20000000000000 : ℝ), (41449534828159/100000000000000 : ℝ), (14694153479993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537568931/1000000000 : ℝ)|^8293 ≤ (8771262335469/20000000000000 : ℝ)^6245
        have hw : |(537568931/1000000000 : ℝ)|=(537568931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030398433/2000000000 : ℝ)|^8293 ≤ (41449534828159/100000000000000 : ℝ)^6245
        have hw : |(1030398433/2000000000 : ℝ)|=(1030398433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-589878561/2500000000 : ℝ)|^8293 ≤ (14694153479993/100000000000000 : ℝ)^6245
        have hw : |(-589878561/2500000000 : ℝ)|=(589878561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s2_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179476129/5000000000 : ℝ)*x 0 + (2005969983/5000000000 : ℝ)*x 1 + (4736056261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179476129/5000000000 : ℝ)^8293 ≤ (33198635451131/100000000000000 : ℝ)^6245 := by
    have hnat : (2179476129 : ℕ)^8293*100000000000000^6245 ≤ 33198635451131^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179476129 5000000000 33198635451131 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005969983/5000000000 : ℝ)^8293 ≤ (29735657263459/100000000000000 : ℝ)^6245 := by
    have hnat : (2005969983 : ℕ)^8293*100000000000000^6245 ≤ 29735657263459^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005969983 5000000000 29735657263459 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4736056261/10000000000 : ℝ)^8293 ≤ (3706570727143/10000000000000 : ℝ)^6245 := by
    have hnat : (4736056261 : ℕ)^8293*10000000000000^6245 ≤ 3706570727143^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4736056261 10000000000 3706570727143 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179476129/5000000000 : ℝ), (2005969983/5000000000 : ℝ), (4736056261/10000000000 : ℝ)] ![(33198635451131/100000000000000 : ℝ), (29735657263459/100000000000000 : ℝ), (3706570727143/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179476129/5000000000 : ℝ)|^8293 ≤ (33198635451131/100000000000000 : ℝ)^6245
        have hw : |(2179476129/5000000000 : ℝ)|=(2179476129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2005969983/5000000000 : ℝ)|^8293 ≤ (29735657263459/100000000000000 : ℝ)^6245
        have hw : |(2005969983/5000000000 : ℝ)|=(2005969983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4736056261/10000000000 : ℝ)|^8293 ≤ (3706570727143/10000000000000 : ℝ)^6245
        have hw : |(4736056261/10000000000 : ℝ)|=(4736056261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s2_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168507049/10000000000 : ℝ)*x 0 + (5154597533/10000000000 : ℝ)*x 1 + (2758176739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168507049/10000000000 : ℝ)^8293 ≤ (6567950412503/50000000000000 : ℝ)^6245 := by
    have hnat : (2168507049 : ℕ)^8293*50000000000000^6245 ≤ 6567950412503^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168507049 10000000000 6567950412503 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5154597533/10000000000 : ℝ)^8293 ≤ (41477372234623/100000000000000 : ℝ)^6245 := by
    have hnat : (5154597533 : ℕ)^8293*100000000000000^6245 ≤ 41477372234623^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154597533 10000000000 41477372234623 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2758176739/5000000000 : ℝ)^8293 ≤ (9077345383797/20000000000000 : ℝ)^6245 := by
    have hnat : (2758176739 : ℕ)^8293*20000000000000^6245 ≤ 9077345383797^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758176739 5000000000 9077345383797 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168507049/10000000000 : ℝ), (5154597533/10000000000 : ℝ), (2758176739/5000000000 : ℝ)] ![(6567950412503/50000000000000 : ℝ), (41477372234623/100000000000000 : ℝ), (9077345383797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168507049/10000000000 : ℝ)|^8293 ≤ (6567950412503/50000000000000 : ℝ)^6245
        have hw : |(-2168507049/10000000000 : ℝ)|=(2168507049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5154597533/10000000000 : ℝ)|^8293 ≤ (41477372234623/100000000000000 : ℝ)^6245
        have hw : |(5154597533/10000000000 : ℝ)|=(5154597533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2758176739/5000000000 : ℝ)|^8293 ≤ (9077345383797/20000000000000 : ℝ)^6245
        have hw : |(2758176739/5000000000 : ℝ)|=(2758176739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s2_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282837143/10000000000 : ℝ)*x 0 + (-399030469/2000000000 : ℝ)*x 1 + (2758176783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282837143/10000000000 : ℝ)^8293 ≤ (42853238436739/100000000000000 : ℝ)^6245 := by
    have hnat : (5282837143 : ℕ)^8293*100000000000000^6245 ≤ 42853238436739^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282837143 10000000000 42853238436739 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399030469/2000000000 : ℝ)^8293 ≤ (2352006734609/20000000000000 : ℝ)^6245 := by
    have hnat : (399030469 : ℕ)^8293*20000000000000^6245 ≤ 2352006734609^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399030469 2000000000 2352006734609 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2758176783/5000000000 : ℝ)^8293 ≤ (45386727880461/100000000000000 : ℝ)^6245 := by
    have hnat : (2758176783 : ℕ)^8293*100000000000000^6245 ≤ 45386727880461^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758176783 5000000000 45386727880461 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282837143/10000000000 : ℝ), (-399030469/2000000000 : ℝ), (2758176783/5000000000 : ℝ)] ![(42853238436739/100000000000000 : ℝ), (2352006734609/20000000000000 : ℝ), (45386727880461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282837143/10000000000 : ℝ)|^8293 ≤ (42853238436739/100000000000000 : ℝ)^6245
        have hw : |(5282837143/10000000000 : ℝ)|=(5282837143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399030469/2000000000 : ℝ)|^8293 ≤ (2352006734609/20000000000000 : ℝ)^6245
        have hw : |(-399030469/2000000000 : ℝ)|=(399030469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2758176783/5000000000 : ℝ)|^8293 ≤ (45386727880461/100000000000000 : ℝ)^6245
        have hw : |(2758176783/5000000000 : ℝ)|=(2758176783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s2_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660354663/1250000000 : ℝ)*x 0 + (5516353497/10000000000 : ℝ)*x 1 + (-1995152219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660354663/1250000000 : ℝ)^8293 ≤ (10713310042757/25000000000000 : ℝ)^6245 := by
    have hnat : (660354663 : ℕ)^8293*25000000000000^6245 ≤ 10713310042757^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660354663 1250000000 10713310042757 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516353497/10000000000 : ℝ)^8293 ≤ (2836670445411/6250000000000 : ℝ)^6245 := by
    have hnat : (5516353497 : ℕ)^8293*6250000000000^6245 ≤ 2836670445411^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516353497 10000000000 2836670445411 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1995152219/10000000000 : ℝ)^8293 ≤ (5880016343403/50000000000000 : ℝ)^6245 := by
    have hnat : (1995152219 : ℕ)^8293*50000000000000^6245 ≤ 5880016343403^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995152219 10000000000 5880016343403 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660354663/1250000000 : ℝ), (5516353497/10000000000 : ℝ), (-1995152219/10000000000 : ℝ)] ![(10713310042757/25000000000000 : ℝ), (2836670445411/6250000000000 : ℝ), (5880016343403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660354663/1250000000 : ℝ)|^8293 ≤ (10713310042757/25000000000000 : ℝ)^6245
        have hw : |(660354663/1250000000 : ℝ)|=(660354663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516353497/10000000000 : ℝ)|^8293 ≤ (2836670445411/6250000000000 : ℝ)^6245
        have hw : |(5516353497/10000000000 : ℝ)|=(5516353497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1995152219/10000000000 : ℝ)|^8293 ≤ (5880016343403/50000000000000 : ℝ)^6245
        have hw : |(-1995152219/10000000000 : ℝ)|=(1995152219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s2_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359179811/10000000000 : ℝ)*x 0 + (4730914131/10000000000 : ℝ)*x 1 + (4017133761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359179811/10000000000 : ℝ)^8293 ≤ (4150117114021/12500000000000 : ℝ)^6245 := by
    have hnat : (4359179811 : ℕ)^8293*12500000000000^6245 ≤ 4150117114021^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359179811 10000000000 4150117114021 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4730914131/10000000000 : ℝ)^8293 ≤ (9253068850471/25000000000000 : ℝ)^6245 := by
    have hnat : (4730914131 : ℕ)^8293*25000000000000^6245 ≤ 9253068850471^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730914131 10000000000 9253068850471 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4017133761/10000000000 : ℝ)^8293 ≤ (14893393837981/50000000000000 : ℝ)^6245 := by
    have hnat : (4017133761 : ℕ)^8293*50000000000000^6245 ≤ 14893393837981^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017133761 10000000000 14893393837981 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359179811/10000000000 : ℝ), (4730914131/10000000000 : ℝ), (4017133761/10000000000 : ℝ)] ![(4150117114021/12500000000000 : ℝ), (9253068850471/25000000000000 : ℝ), (14893393837981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359179811/10000000000 : ℝ)|^8293 ≤ (4150117114021/12500000000000 : ℝ)^6245
        have hw : |(4359179811/10000000000 : ℝ)|=(4359179811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4730914131/10000000000 : ℝ)|^8293 ≤ (9253068850471/25000000000000 : ℝ)^6245
        have hw : |(4730914131/10000000000 : ℝ)|=(4730914131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4017133761/10000000000 : ℝ)|^8293 ≤ (14893393837981/50000000000000 : ℝ)^6245
        have hw : |(4017133761/10000000000 : ℝ)|=(4017133761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2063/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2219/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16631/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2063/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5411/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2063/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5411/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2063/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5411/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2063/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5411/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2063/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5411/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2063/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5411/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5411/100000 : ℝ) ^ (2073/512 : ℝ) ≤ (185865361829851/25000000000000000000 : ℝ) := by
    have hpowers : (5411/100000 : ℝ)^2073 ≤ (185865361829851/25000000000000000000 : ℝ)^512 := by
      have hnat : (5411 : ℕ)^2073*25000000000000000000^512 ≤ 185865361829851^512*100000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5411 100000 185865361829851 25000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5411/100000 : ℝ)) (X := (185865361829851/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2063/10000 : ℝ) ^ (2073/512 : ℝ) ≤ (167696961812616603/100000000000000000000 : ℝ) := by
    have hpowers : (2063/10000 : ℝ)^2073 ≤ (167696961812616603/100000000000000000000 : ℝ)^512 := by
      have hnat : (2063 : ℕ)^2073*100000000000000000000^512 ≤ 167696961812616603^512*10000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2063 10000 167696961812616603 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2063/10000 : ℝ)) (X := (167696961812616603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500185865361829851/12500000000000000000 : ℝ) ≤ (10000036724566331/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (12500185865361829851/12500000000000000000 : ℝ)^512 ≤ (10000036724566331/10000000000000000 : ℝ)^2073 := by
      have hnat : (12500185865361829851 : ℕ)^512*10000000000000000^2073 ≤ 10000036724566331^2073*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500185865361829851 12500000000000000000 10000036724566331 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036724566331/10000000000000000 : ℝ)) (X := (12500185865361829851/12500000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100168440423259936007/100000000000000000000 : ℝ) ≤ (10004157590782287/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (100168440423259936007/100000000000000000000 : ℝ)^512 ≤ (10004157590782287/10000000000000000 : ℝ)^2073 := by
      have hnat : (100168440423259936007 : ℕ)^512*10000000000000000^2073 ≤ 10004157590782287^2073*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100168440423259936007 100000000000000000000 10004157590782287 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004157590782287/10000000000000000 : ℝ)) (X := (100168440423259936007/100000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50167696961812616603/50000000000000000000 : ℝ) ≤ (10008278456998243/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50167696961812616603/50000000000000000000 : ℝ)^512 ≤ (10008278456998243/10000000000000000 : ℝ)^2073 := by
      have hnat : (50167696961812616603 : ℕ)^512*10000000000000000^2073 ≤ 10008278456998243^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50167696961812616603 50000000000000000000 10008278456998243 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008278456998243/10000000000000000 : ℝ)) (X := (50167696961812616603/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(185865361829851/25000000000000000000 : ℝ) ≤ ((152145962896985915657/152190000000000000000 : ℝ)+2*(1030216553989/380475000000000 : ℝ)*(5411/100000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (152145962896985915657/152190000000000000000 : ℝ)+2*(1030216553989/380475000000000 : ℝ)*(5411/100000 : ℝ)=(10000036724566331/10000000000000000 : ℝ) by norm_num, show 1+2*(185865361829851/25000000000000000000 : ℝ)=(12500185865361829851/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(167696961812616603/100000000000000000000 : ℝ)+(185865361829851/25000000000000000000 : ℝ) ≤ ((152145962896985915657/152190000000000000000 : ℝ)+(1030216553989/380475000000000 : ℝ)*((2063/10000 : ℝ)+(5411/100000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (152145962896985915657/152190000000000000000 : ℝ)+(1030216553989/380475000000000 : ℝ)*((2063/10000 : ℝ)+(5411/100000 : ℝ))=(10004157590782287/10000000000000000 : ℝ) by norm_num, show 1+(167696961812616603/100000000000000000000 : ℝ)+(185865361829851/25000000000000000000 : ℝ)=(100168440423259936007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(167696961812616603/100000000000000000000 : ℝ) ≤ ((152145962896985915657/152190000000000000000 : ℝ)+2*(1030216553989/380475000000000 : ℝ)*(2063/10000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (152145962896985915657/152190000000000000000 : ℝ)+2*(1030216553989/380475000000000 : ℝ)*(2063/10000 : ℝ)=(10008278456998243/10000000000000000 : ℝ) by norm_num, show 1+2*(167696961812616603/100000000000000000000 : ℝ)=(50167696961812616603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (152145962896985915657/152190000000000000000 : ℝ)*(X 1 0+X 2 0)+(1030216553989/380475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5411/100000 : ℝ)) (hi := (2063/10000 : ℝ)) (c := (152145962896985915657/152190000000000000000 : ℝ)) (alpha := (1030216553989/380475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (152145962896985915657/152190000000000000000 : ℝ)*(X 0 1+X 2 1)+(1030216553989/380475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5411/100000 : ℝ)) (hi := (2063/10000 : ℝ)) (c := (152145962896985915657/152190000000000000000 : ℝ)) (alpha := (1030216553989/380475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (152145962896985915657/152190000000000000000 : ℝ)*(X 0 2+X 1 2)+(1030216553989/380475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5411/100000 : ℝ)) (hi := (2063/10000 : ℝ)) (c := (152145962896985915657/152190000000000000000 : ℝ)) (alpha := (1030216553989/380475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-542098097/2500000000 : ℝ)*X 0 0+(5518986669/10000000000 : ℝ)*X 0 1+(1287997751/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075137871/2000000000 : ℝ)*X 1 0+(-2359514249/10000000000 : ℝ)*X 1 1+(1030398423/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537568931/1000000000 : ℝ)*X 2 0+(1030398433/2000000000 : ℝ)*X 2 1+(-589878561/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179476129/5000000000 : ℝ)*X 0 0+(2005969983/5000000000 : ℝ)*X 0 1+(4736056261/10000000000 : ℝ)*X 0 2+(2179476129/5000000000 : ℝ)*X 1 0+(2005969983/5000000000 : ℝ)*X 1 1+(4736056261/10000000000 : ℝ)*X 1 2+(2179476129/5000000000 : ℝ)*X 2 0+(2005969983/5000000000 : ℝ)*X 2 1+(4736056261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2168507049/10000000000 : ℝ)*X 0 0+(5154597533/10000000000 : ℝ)*X 0 1+(2758176739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282837143/10000000000 : ℝ)*X 1 0+(-399030469/2000000000 : ℝ)*X 1 1+(2758176783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660354663/1250000000 : ℝ)*X 2 0+(5516353497/10000000000 : ℝ)*X 2 1+(-1995152219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359179811/10000000000 : ℝ)*X 0 0+(4730914131/10000000000 : ℝ)*X 0 1+(4017133761/10000000000 : ℝ)*X 0 2+(4359179811/10000000000 : ℝ)*X 1 0+(4730914131/10000000000 : ℝ)*X 1 1+(4017133761/10000000000 : ℝ)*X 1 2+(4359179811/10000000000 : ℝ)*X 2 0+(4730914131/10000000000 : ℝ)*X 2 1+(4017133761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (504657104659241368116169679/84550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133749893/25000000000000 : ℝ)*(base19) + (155765597/50000000000000 : ℝ)*(base23) + (17312573/100000000000000 : ℝ)*(upper2) + (19501309/12500000000000 : ℝ)*(upper3) + (125180399/100000000000000 : ℝ)*(upper4) + (410585359439659/20000000000000 : ℝ)*(major0) + (410585359439659/20000000000000 : ℝ)*(major1) + (410585359439659/20000000000000 : ℝ)*(major2) + (272484048226611/10000000000000 : ℝ)*(sp0) + (1362425546226319/50000000000000 : ℝ)*(sp1) + (340606414490127/12500000000000 : ℝ)*(sp2) + (690498474197299/50000000000000 : ℝ)*(sp3) + (111451861/1000000000000 : ℝ)*(sp4) + (4819591721/100000000000000 : ℝ)*(sp7) + (1381001767986319/100000000000000 : ℝ)*(f.failure) + (272485162745221/10000000000000 : ℝ)*(f.sum) + (52725466695739/15219000000000000000000000000 : ℝ)*base65 + (9921005765771689/11400000000000000000000000000000 : ℝ)*base67 + (39613343279771689/11400000000000000000000000000000 : ℝ)*base69 + (67197757911371689/11400000000000000000000000000000 : ℝ)*base71 + (16599870381721/15219000000000000000000000000 : ℝ)*base73 + (27750285197771689/11400000000000000000000000000000 : ℝ)*base75 + (64783125446628311/11400000000000000000000000000000 : ℝ)*base78 + (166050153215771689/11400000000000000000000000000000 : ℝ)*base79 + (90790294744759/15219000000000000000000000000 : ℝ)*base81 + (476869/100000000000000000000 : ℝ)*base90 + (476869/100000000000000000000 : ℝ)*base92 + (476869/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3889900679933347264357/792656250000000000000000000 : ℝ) := by norm_num
    linear_combination (487799349/50000000000000 : ℝ)*(base19) + (1162444537/100000000000000 : ℝ)*(base23) + (143874981/100000000000000 : ℝ)*(upper3) + (31484957/100000000000000 : ℝ)*(lower4) + (44731159/50000000000000 : ℝ)*(upper5) + (2082642810121711/100000000000000 : ℝ)*(major0) + (2082642810121711/100000000000000 : ℝ)*(major1) + (2082642810121711/100000000000000 : ℝ)*(major2) + (4362080083/50000000000000 : ℝ)*(sp1) + (5585409923/50000000000000 : ℝ)*(sp2) + (1382146878506737/50000000000000 : ℝ)*(sp4) + (276428405725461/10000000000000 : ℝ)*(sp5) + (691070355937273/25000000000000 : ℝ)*(sp6) + (175123962456141/12500000000000 : ℝ)*(sp7) + (175123962456141/12500000000000 : ℝ)*(f.failure) + (1382146878506737/50000000000000 : ℝ)*(f.sum) + (7578167106713/38047500000000000000000000000 : ℝ)*base65 + (44257155961677419/57000000000000000000000000000000 : ℝ)*base68 + (513642566548322581/57000000000000000000000000000000 : ℝ)*base69 + (158869209232322581/57000000000000000000000000000000 : ℝ)*base71 + (48600143862941/19023750000000000000000000000 : ℝ)*base74 + (110095803202322581/57000000000000000000000000000000 : ℝ)*base75 + (230700828643677419/57000000000000000000000000000000 : ℝ)*base78 + (112379091265677419/57000000000000000000000000000000 : ℝ)*base80 + (15497052202831/4755937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (72409/12500000000000000000 : ℝ)*base89 + (72409/12500000000000000000 : ℝ)*base91 + (72409/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1100_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2063/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2219/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16631/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1100_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2219/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16631/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1100_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1100_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1100_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2219/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16631/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
