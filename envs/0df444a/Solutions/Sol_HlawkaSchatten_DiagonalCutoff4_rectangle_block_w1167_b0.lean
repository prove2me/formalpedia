-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:09.487279+00:00
-- url     : https://prove2.me/submissions/06c49ea4-b1ec-4ebe-813a-4470f0cb4855

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
theorem support_rectangle_w1167_s0_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-941961743/5000000000 : ℝ)*x 0 + (6048570073/10000000000 : ℝ)*x 1 + (4783625901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941961743/5000000000 : ℝ)^1045 ≤ (1370122268103/12500000000000 : ℝ)^789 := by
    have hnat : (941961743 : ℕ)^1045*12500000000000^789 ≤ 1370122268103^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941961743 5000000000 1370122268103 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6048570073/10000000000 : ℝ)^1045 ≤ (6422697625809/12500000000000 : ℝ)^789 := by
    have hnat : (6048570073 : ℕ)^1045*12500000000000^789 ≤ 6422697625809^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6048570073 10000000000 6422697625809 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783625901/10000000000 : ℝ)^1045 ≤ (18828720416847/50000000000000 : ℝ)^789 := by
    have hnat : (4783625901 : ℕ)^1045*50000000000000^789 ≤ 18828720416847^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783625901 10000000000 18828720416847 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941961743/5000000000 : ℝ), (6048570073/10000000000 : ℝ), (4783625901/10000000000 : ℝ)] ![(1370122268103/12500000000000 : ℝ), (6422697625809/12500000000000 : ℝ), (18828720416847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941961743/5000000000 : ℝ)|^1045 ≤ (1370122268103/12500000000000 : ℝ)^789
        have hw : |(-941961743/5000000000 : ℝ)|=(941961743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6048570073/10000000000 : ℝ)|^1045 ≤ (6422697625809/12500000000000 : ℝ)^789
        have hw : |(6048570073/10000000000 : ℝ)|=(6048570073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783625901/10000000000 : ℝ)|^1045 ≤ (18828720416847/50000000000000 : ℝ)^789
        have hw : |(4783625901/10000000000 : ℝ)|=(4783625901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s0_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5515385257/10000000000 : ℝ)*x 0 + (-1304573519/5000000000 : ℝ)*x 1 + (4783625877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515385257/10000000000 : ℝ)^1045 ≤ (45470235995669/100000000000000 : ℝ)^789 := by
    have hnat : (5515385257 : ℕ)^1045*100000000000000^789 ≤ 45470235995669^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515385257 10000000000 45470235995669 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304573519/5000000000 : ℝ)^1045 ≤ (8436161705159/50000000000000 : ℝ)^789 := by
    have hnat : (1304573519 : ℕ)^1045*50000000000000^789 ≤ 8436161705159^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304573519 5000000000 8436161705159 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783625877/10000000000 : ℝ)^1045 ≤ (37657440583461/100000000000000 : ℝ)^789 := by
    have hnat : (4783625877 : ℕ)^1045*100000000000000^789 ≤ 37657440583461^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783625877 10000000000 37657440583461 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515385257/10000000000 : ℝ), (-1304573519/5000000000 : ℝ), (4783625877/10000000000 : ℝ)] ![(45470235995669/100000000000000 : ℝ), (8436161705159/50000000000000 : ℝ), (37657440583461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515385257/10000000000 : ℝ)|^1045 ≤ (45470235995669/100000000000000 : ℝ)^789
        have hw : |(5515385257/10000000000 : ℝ)|=(5515385257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1304573519/5000000000 : ℝ)|^1045 ≤ (8436161705159/50000000000000 : ℝ)^789
        have hw : |(-1304573519/5000000000 : ℝ)|=(1304573519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783625877/10000000000 : ℝ)|^1045 ≤ (37657440583461/100000000000000 : ℝ)^789
        have hw : |(4783625877/10000000000 : ℝ)|=(4783625877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s0_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (275769261/500000000 : ℝ)*x 0 + (2391812957/5000000000 : ℝ)*x 1 + (-16307169/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275769261/500000000 : ℝ)^1045 ≤ (45470235591659/100000000000000 : ℝ)^789 := by
    have hnat : (275769261 : ℕ)^1045*100000000000000^789 ≤ 45470235591659^789*500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275769261 500000000 45470235591659 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2391812957/5000000000 : ℝ)^1045 ≤ (37657440969237/100000000000000 : ℝ)^789 := by
    have hnat : (2391812957 : ℕ)^1045*100000000000000^789 ≤ 37657440969237^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391812957 5000000000 37657440969237 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16307169/62500000 : ℝ)^1045 ≤ (16872323427447/100000000000000 : ℝ)^789 := by
    have hnat : (16307169 : ℕ)^1045*100000000000000^789 ≤ 16872323427447^789*62500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16307169 62500000 16872323427447 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275769261/500000000 : ℝ), (2391812957/5000000000 : ℝ), (-16307169/62500000 : ℝ)] ![(45470235591659/100000000000000 : ℝ), (37657440969237/100000000000000 : ℝ), (16872323427447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275769261/500000000 : ℝ)|^1045 ≤ (45470235591659/100000000000000 : ℝ)^789
        have hw : |(275769261/500000000 : ℝ)|=(275769261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2391812957/5000000000 : ℝ)|^1045 ≤ (37657440969237/100000000000000 : ℝ)^789
        have hw : |(2391812957/5000000000 : ℝ)|=(2391812957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16307169/62500000 : ℝ)|^1045 ≤ (16872323427447/100000000000000 : ℝ)^789
        have hw : |(-16307169/62500000 : ℝ)|=(16307169/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s0_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2099488201/5000000000 : ℝ)*x 0 + (6239897/20000000 : ℝ)*x 1 + (5648868369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099488201/5000000000 : ℝ)^1045 ≤ (31686045843641/100000000000000 : ℝ)^789 := by
    have hnat : (2099488201 : ℕ)^1045*100000000000000^789 ≤ 31686045843641^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099488201 5000000000 31686045843641 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6239897/20000000 : ℝ)^1045 ≤ (855219925213/4000000000000 : ℝ)^789 := by
    have hnat : (6239897 : ℕ)^1045*4000000000000^789 ≤ 855219925213^789*20000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6239897 20000000 855219925213 4000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5648868369/10000000000 : ℝ)^1045 ≤ (23466728004011/50000000000000 : ℝ)^789 := by
    have hnat : (5648868369 : ℕ)^1045*50000000000000^789 ≤ 23466728004011^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648868369 10000000000 23466728004011 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099488201/5000000000 : ℝ), (6239897/20000000 : ℝ), (5648868369/10000000000 : ℝ)] ![(31686045843641/100000000000000 : ℝ), (855219925213/4000000000000 : ℝ), (23466728004011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099488201/5000000000 : ℝ)|^1045 ≤ (31686045843641/100000000000000 : ℝ)^789
        have hw : |(2099488201/5000000000 : ℝ)|=(2099488201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6239897/20000000 : ℝ)|^1045 ≤ (855219925213/4000000000000 : ℝ)^789
        have hw : |(6239897/20000000 : ℝ)|=(6239897/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5648868369/10000000000 : ℝ)|^1045 ≤ (23466728004011/50000000000000 : ℝ)^789
        have hw : |(5648868369/10000000000 : ℝ)|=(5648868369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s0_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-472248973/2500000000 : ℝ)*x 0 + (1204061247/2500000000 : ℝ)*x 1 + (187962573/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472248973/2500000000 : ℝ)^1045 ≤ (2200016567739/20000000000000 : ℝ)^789 := by
    have hnat : (472248973 : ℕ)^1045*20000000000000^789 ≤ 2200016567739^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472248973 2500000000 2200016567739 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204061247/2500000000 : ℝ)^1045 ≤ (37997914959633/100000000000000 : ℝ)^789 := by
    have hnat : (1204061247 : ℕ)^1045*100000000000000^789 ≤ 37997914959633^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204061247 2500000000 37997914959633 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187962573/312500000 : ℝ)^1045 ≤ (10200400436131/20000000000000 : ℝ)^789 := by
    have hnat : (187962573 : ℕ)^1045*20000000000000^789 ≤ 10200400436131^789*312500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187962573 312500000 10200400436131 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472248973/2500000000 : ℝ), (1204061247/2500000000 : ℝ), (187962573/312500000 : ℝ)] ![(2200016567739/20000000000000 : ℝ), (37997914959633/100000000000000 : ℝ), (10200400436131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472248973/2500000000 : ℝ)|^1045 ≤ (2200016567739/20000000000000 : ℝ)^789
        have hw : |(-472248973/2500000000 : ℝ)|=(472248973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204061247/2500000000 : ℝ)|^1045 ≤ (37997914959633/100000000000000 : ℝ)^789
        have hw : |(1204061247/2500000000 : ℝ)|=(1204061247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187962573/312500000 : ℝ)|^1045 ≤ (10200400436131/20000000000000 : ℝ)^789
        have hw : |(187962573/312500000 : ℝ)|=(187962573/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s0_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5171551271/10000000000 : ℝ)*x 0 + (-172246351/1250000000 : ℝ)*x 1 + (3007401057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171551271/10000000000 : ℝ)^1045 ≤ (41754363327401/100000000000000 : ℝ)^789 := by
    have hnat : (5171551271 : ℕ)^1045*100000000000000^789 ≤ 41754363327401^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171551271 10000000000 41754363327401 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172246351/1250000000 : ℝ)^1045 ≤ (362181848677/5000000000000 : ℝ)^789 := by
    have hnat : (172246351 : ℕ)^1045*5000000000000^789 ≤ 362181848677^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172246351 1250000000 362181848677 5000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3007401057/5000000000 : ℝ)^1045 ≤ (51001999687449/100000000000000 : ℝ)^789 := by
    have hnat : (3007401057 : ℕ)^1045*100000000000000^789 ≤ 51001999687449^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007401057 5000000000 51001999687449 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171551271/10000000000 : ℝ), (-172246351/1250000000 : ℝ), (3007401057/5000000000 : ℝ)] ![(41754363327401/100000000000000 : ℝ), (362181848677/5000000000000 : ℝ), (51001999687449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171551271/10000000000 : ℝ)|^1045 ≤ (41754363327401/100000000000000 : ℝ)^789
        have hw : |(5171551271/10000000000 : ℝ)|=(5171551271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172246351/1250000000 : ℝ)|^1045 ≤ (362181848677/5000000000000 : ℝ)^789
        have hw : |(-172246351/1250000000 : ℝ)|=(172246351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3007401057/5000000000 : ℝ)|^1045 ≤ (51001999687449/100000000000000 : ℝ)^789
        have hw : |(3007401057/5000000000 : ℝ)|=(3007401057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s0_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5171551237/10000000000 : ℝ)*x 0 + (187962569/312500000 : ℝ)*x 1 + (-344492677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171551237/10000000000 : ℝ)^1045 ≤ (41754362963821/100000000000000 : ℝ)^789 := by
    have hnat : (5171551237 : ℕ)^1045*100000000000000^789 ≤ 41754362963821^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171551237 10000000000 41754362963821 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187962569/312500000 : ℝ)^1045 ≤ (51002000743131/100000000000000 : ℝ)^789 := by
    have hnat : (187962569 : ℕ)^1045*100000000000000^789 ≤ 51002000743131^789*312500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187962569 312500000 51002000743131 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344492677/2500000000 : ℝ)^1045 ≤ (1448727255461/20000000000000 : ℝ)^789 := by
    have hnat : (344492677 : ℕ)^1045*20000000000000^789 ≤ 1448727255461^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344492677 2500000000 1448727255461 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171551237/10000000000 : ℝ), (187962569/312500000 : ℝ), (-344492677/2500000000 : ℝ)] ![(41754362963821/100000000000000 : ℝ), (51002000743131/100000000000000 : ℝ), (1448727255461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171551237/10000000000 : ℝ)|^1045 ≤ (41754362963821/100000000000000 : ℝ)^789
        have hw : |(5171551237/10000000000 : ℝ)|=(5171551237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187962569/312500000 : ℝ)|^1045 ≤ (51002000743131/100000000000000 : ℝ)^789
        have hw : |(187962569/312500000 : ℝ)|=(187962569/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-344492677/2500000000 : ℝ)|^1045 ≤ (1448727255461/20000000000000 : ℝ)^789
        have hw : |(-344492677/2500000000 : ℝ)|=(344492677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s0_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (841823509/2000000000 : ℝ)*x 0 + (2791827461/5000000000 : ℝ)*x 1 + (3187458351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841823509/2000000000 : ℝ)^1045 ≤ (31787441848093/100000000000000 : ℝ)^789 := by
    have hnat : (841823509 : ℕ)^1045*100000000000000^789 ≤ 31787441848093^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841823509 2000000000 31787441848093 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2791827461/5000000000 : ℝ)^1045 ≤ (46217178599557/100000000000000 : ℝ)^789 := by
    have hnat : (2791827461 : ℕ)^1045*100000000000000^789 ≤ 46217178599557^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791827461 5000000000 46217178599557 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187458351/10000000000 : ℝ)^1045 ≤ (21995379534287/100000000000000 : ℝ)^789 := by
    have hnat : (3187458351 : ℕ)^1045*100000000000000^789 ≤ 21995379534287^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187458351 10000000000 21995379534287 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841823509/2000000000 : ℝ), (2791827461/5000000000 : ℝ), (3187458351/10000000000 : ℝ)] ![(31787441848093/100000000000000 : ℝ), (46217178599557/100000000000000 : ℝ), (21995379534287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841823509/2000000000 : ℝ)|^1045 ≤ (31787441848093/100000000000000 : ℝ)^789
        have hw : |(841823509/2000000000 : ℝ)|=(841823509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2791827461/5000000000 : ℝ)|^1045 ≤ (46217178599557/100000000000000 : ℝ)^789
        have hw : |(2791827461/5000000000 : ℝ)|=(2791827461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187458351/10000000000 : ℝ)|^1045 ≤ (21995379534287/100000000000000 : ℝ)^789
        have hw : |(3187458351/10000000000 : ℝ)|=(3187458351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (129/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (693/2500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8359/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8359 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8359*1^2048 ≤ 0^2048*1^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8359/2048 : ℝ) ≤ (593923848424493531/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8359 ≤ (593923848424493531/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8359*25000000000000000000^2048 ≤ 593923848424493531^2048*5^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 593923848424493531 25000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (593923848424493531/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8359 := by
      have hnat : (1 : ℕ)^2048*1^8359 ≤ 1^8359*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25593923848424493531/25000000000000000000 : ℝ) ≤ (1005769095350863/1000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (25593923848424493531/25000000000000000000 : ℝ)^2048 ≤ (1005769095350863/1000000000000000 : ℝ)^8359 := by
      have hnat : (25593923848424493531 : ℕ)^2048*1000000000000000^8359 ≤ 1005769095350863^8359*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25593923848424493531 25000000000000000000 1005769095350863 1000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005769095350863/1000000000000000 : ℝ)) (X := (25593923848424493531/25000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13093923848424493531/12500000000000000000 : ℝ) ≤ (505769095350863/500000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (13093923848424493531/12500000000000000000 : ℝ)^2048 ≤ (505769095350863/500000000000000 : ℝ)^8359 := by
      have hnat : (13093923848424493531 : ℕ)^2048*500000000000000^8359 ≤ 505769095350863^8359*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13093923848424493531 12500000000000000000 505769095350863 500000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505769095350863/500000000000000 : ℝ)) (X := (13093923848424493531/12500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5769095350863/400000000000000 : ℝ)*(0 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(5769095350863/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(593923848424493531/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5769095350863/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (1 : ℝ)+(5769095350863/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1005769095350863/1000000000000000 : ℝ) by norm_num, show 1+(593923848424493531/25000000000000000000 : ℝ)+(0 : ℝ)=(25593923848424493531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(593923848424493531/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5769095350863/400000000000000 : ℝ)*(2/5 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(5769095350863/400000000000000 : ℝ)*(2/5 : ℝ)=(505769095350863/500000000000000 : ℝ) by norm_num, show 1+2*(593923848424493531/25000000000000000000 : ℝ)=(13093923848424493531/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5769095350863/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5769095350863/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5769095350863/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5769095350863/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5769095350863/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5769095350863/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-941961743/5000000000 : ℝ)*X 0 0+(6048570073/10000000000 : ℝ)*X 0 1+(4783625901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5515385257/10000000000 : ℝ)*X 1 0+(-1304573519/5000000000 : ℝ)*X 1 1+(4783625877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((275769261/500000000 : ℝ)*X 2 0+(2391812957/5000000000 : ℝ)*X 2 1+(-16307169/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099488201/5000000000 : ℝ)*X 0 0+(6239897/20000000 : ℝ)*X 0 1+(5648868369/10000000000 : ℝ)*X 0 2+(2099488201/5000000000 : ℝ)*X 1 0+(6239897/20000000 : ℝ)*X 1 1+(5648868369/10000000000 : ℝ)*X 1 2+(2099488201/5000000000 : ℝ)*X 2 0+(6239897/20000000 : ℝ)*X 2 1+(5648868369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-472248973/2500000000 : ℝ)*X 0 0+(1204061247/2500000000 : ℝ)*X 0 1+(187962573/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171551271/10000000000 : ℝ)*X 1 0+(-172246351/1250000000 : ℝ)*X 1 1+(3007401057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171551237/10000000000 : ℝ)*X 2 0+(187962569/312500000 : ℝ)*X 2 1+(-344492677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((841823509/2000000000 : ℝ)*X 0 0+(2791827461/5000000000 : ℝ)*X 0 1+(3187458351/10000000000 : ℝ)*X 0 2+(841823509/2000000000 : ℝ)*X 1 0+(2791827461/5000000000 : ℝ)*X 1 1+(3187458351/10000000000 : ℝ)*X 1 2+(841823509/2000000000 : ℝ)*X 2 0+(2791827461/5000000000 : ℝ)*X 2 1+(3187458351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5352262180090552389561/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5262067/12500000000000 : ℝ)*(base1) + (536778817/50000000000000 : ℝ)*(base19) + (995758467/100000000000000 : ℝ)*(base23) + (72495733/100000000000000 : ℝ)*(base24) + (15247369/6250000000000 : ℝ)*(upper3) + (37061987788533/6250000000000 : ℝ)*(major0) + (37061987788533/6250000000000 : ℝ)*(major1) + (37061987788533/6250000000000 : ℝ)*(major2) + (790552342623253/100000000000000 : ℝ)*(sp0) + (39527680752617/5000000000000 : ℝ)*(sp1) + (395276810177887/50000000000000 : ℝ)*(sp2) + (395426850374037/100000000000000 : ℝ)*(sp3) + (2388083257/100000000000000 : ℝ)*(sp4) + (377085103/20000000000000 : ℝ)*(sp7) + (49428597237011/12500000000000 : ℝ)*(f.failure) + (395277344304987/50000000000000 : ℝ)*(f.sum) + (253711129771/1250000000000000000000000000 : ℝ)*base66 + (7825673733521/2500000000000000000000000000 : ℝ)*base68 + (4253731253521/2500000000000000000000000000 : ℝ)*base70 + (9323384268521/2500000000000000000000000000 : ℝ)*base72 + (827507541479/1250000000000000000000000000 : ℝ)*base73 + (167174058979/2500000000000000000000000000 : ℝ)*base75 + (3678156518521/2500000000000000000000000000 : ℝ)*base78 + (9183808861021/2500000000000000000000000000 : ℝ)*base80 + (1646357518521/1250000000000000000000000000 : ℝ)*base82 + (5846471/625000000000000000000 : ℝ)*base89 + (5846471/625000000000000000000 : ℝ)*base91 + (5846471/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89400633658187696805819/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103541329/100000000000000 : ℝ)*(base1) + (1109489003/50000000000000 : ℝ)*(base19) + (2214323059/100000000000000 : ℝ)*(base23) + (60868267/25000000000000 : ℝ)*(upper3) + (65290891/25000000000000 : ℝ)*(upper5) + (312916193388071/50000000000000 : ℝ)*(major0) + (312916193388071/50000000000000 : ℝ)*(major1) + (312916193388071/50000000000000 : ℝ)*(major2) + (909753179/20000000000000 : ℝ)*(sp1) + (456125471/10000000000000 : ℝ)*(sp2) + (417168245671889/50000000000000 : ℝ)*(sp4) + (208582405014637/25000000000000 : ℝ)*(sp5) + (20858240305617/2500000000000 : ℝ)*(sp6) + (83465596841277/20000000000000 : ℝ)*(sp7) + (417328087747713/100000000000000 : ℝ)*(f.failure) + (16686727756049/2000000000000 : ℝ)*(f.sum) + (10201184734727/10000000000000000000000000000 : ℝ)*base66 + (13104768924727/20000000000000000000000000000 : ℝ)*base68 + (34441732895273/20000000000000000000000000000 : ℝ)*base69 + (8888523204727/20000000000000000000000000000 : ℝ)*base72 + (11968948004727/10000000000000000000000000000 : ℝ)*base74 + (127286333315273/20000000000000000000000000000 : ℝ)*base75 + (19570339944727/20000000000000000000000000000 : ℝ)*base78 + (107111956755273/20000000000000000000000000000 : ℝ)*base79 + (18441070805273/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (28479107/5000000000000000000000 : ℝ)*base90 + (28479107/5000000000000000000000 : ℝ)*base92 + (28479107/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1167_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (129/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (693/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1167_s1_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1043386463/5000000000 : ℝ)*x 0 + (1423722467/2500000000 : ℝ)*x 1 + (5007450603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043386463/5000000000 : ℝ)^1045 ≤ (627539698697/5000000000000 : ℝ)^789 := by
    have hnat : (1043386463 : ℕ)^1045*5000000000000^789 ≤ 627539698697^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043386463 5000000000 627539698697 5000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423722467/2500000000 : ℝ)^1045 ≤ (47440556120707/100000000000000 : ℝ)^789 := by
    have hnat : (1423722467 : ℕ)^1045*100000000000000^789 ≤ 47440556120707^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423722467 2500000000 47440556120707 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5007450603/10000000000 : ℝ)^1045 ≤ (1600345995837/4000000000000 : ℝ)^789 := by
    have hnat : (5007450603 : ℕ)^1045*4000000000000^789 ≤ 1600345995837^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007450603 10000000000 1600345995837 4000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1043386463/5000000000 : ℝ), (1423722467/2500000000 : ℝ), (5007450603/10000000000 : ℝ)] ![(627539698697/5000000000000 : ℝ), (47440556120707/100000000000000 : ℝ), (1600345995837/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1043386463/5000000000 : ℝ)|^1045 ≤ (627539698697/5000000000000 : ℝ)^789
        have hw : |(-1043386463/5000000000 : ℝ)|=(1043386463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423722467/2500000000 : ℝ)|^1045 ≤ (47440556120707/100000000000000 : ℝ)^789
        have hw : |(1423722467/2500000000 : ℝ)|=(1423722467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5007450603/10000000000 : ℝ)|^1045 ≤ (1600345995837/4000000000000 : ℝ)^789
        have hw : |(5007450603/10000000000 : ℝ)|=(5007450603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s1_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (541775409/1000000000 : ℝ)*x 0 + (-1228642361/5000000000 : ℝ)*x 1 + (5007449643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541775409/1000000000 : ℝ)^1045 ≤ (22203627961881/50000000000000 : ℝ)^789 := by
    have hnat : (541775409 : ℕ)^1045*50000000000000^789 ≤ 22203627961881^789*1000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541775409 1000000000 22203627961881 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1228642361/5000000000 : ℝ)^1045 ≤ (7792052160677/50000000000000 : ℝ)^789 := by
    have hnat : (1228642361 : ℕ)^1045*50000000000000^789 ≤ 7792052160677^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228642361 5000000000 7792052160677 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5007449643/10000000000 : ℝ)^1045 ≤ (40008639737001/100000000000000 : ℝ)^789 := by
    have hnat : (5007449643 : ℕ)^1045*100000000000000^789 ≤ 40008639737001^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007449643 10000000000 40008639737001 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541775409/1000000000 : ℝ), (-1228642361/5000000000 : ℝ), (5007449643/10000000000 : ℝ)] ![(22203627961881/50000000000000 : ℝ), (7792052160677/50000000000000 : ℝ), (40008639737001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541775409/1000000000 : ℝ)|^1045 ≤ (22203627961881/50000000000000 : ℝ)^789
        have hw : |(541775409/1000000000 : ℝ)|=(541775409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1228642361/5000000000 : ℝ)|^1045 ≤ (7792052160677/50000000000000 : ℝ)^789
        have hw : |(-1228642361/5000000000 : ℝ)|=(1228642361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5007449643/10000000000 : ℝ)|^1045 ≤ (40008639737001/100000000000000 : ℝ)^789
        have hw : |(5007449643/10000000000 : ℝ)|=(5007449643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s1_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2708878103/5000000000 : ℝ)*x 0 + (5007447693/10000000000 : ℝ)*x 1 + (-491456889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708878103/5000000000 : ℝ)^1045 ≤ (44407278895277/100000000000000 : ℝ)^789 := by
    have hnat : (2708878103 : ℕ)^1045*100000000000000^789 ≤ 44407278895277^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708878103 5000000000 44407278895277 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5007447693/10000000000 : ℝ)^1045 ≤ (40008619101687/100000000000000 : ℝ)^789 := by
    have hnat : (5007447693 : ℕ)^1045*100000000000000^789 ≤ 40008619101687^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007447693 10000000000 40008619101687 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491456889/2000000000 : ℝ)^1045 ≤ (15584101994627/100000000000000 : ℝ)^789 := by
    have hnat : (491456889 : ℕ)^1045*100000000000000^789 ≤ 15584101994627^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491456889 2000000000 15584101994627 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708878103/5000000000 : ℝ), (5007447693/10000000000 : ℝ), (-491456889/2000000000 : ℝ)] ![(44407278895277/100000000000000 : ℝ), (40008619101687/100000000000000 : ℝ), (15584101994627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708878103/5000000000 : ℝ)|^1045 ≤ (44407278895277/100000000000000 : ℝ)^789
        have hw : |(2708878103/5000000000 : ℝ)|=(2708878103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5007447693/10000000000 : ℝ)|^1045 ≤ (40008619101687/100000000000000 : ℝ)^789
        have hw : |(5007447693/10000000000 : ℝ)|=(5007447693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491456889/2000000000 : ℝ)|^1045 ≤ (15584101994627/100000000000000 : ℝ)^789
        have hw : |(-491456889/2000000000 : ℝ)|=(491456889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s1_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (863062469/2000000000 : ℝ)*x 0 + (3681693717/10000000000 : ℝ)*x 1 + (2528020521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863062469/2000000000 : ℝ)^1045 ≤ (32853966905917/100000000000000 : ℝ)^789 := by
    have hnat : (863062469 : ℕ)^1045*100000000000000^789 ≤ 32853966905917^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863062469 2000000000 32853966905917 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3681693717/10000000000 : ℝ)^1045 ≤ (332779763653/1250000000000 : ℝ)^789 := by
    have hnat : (3681693717 : ℕ)^1045*1250000000000^789 ≤ 332779763653^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681693717 10000000000 332779763653 1250000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2528020521/5000000000 : ℝ)^1045 ≤ (40523651980709/100000000000000 : ℝ)^789 := by
    have hnat : (2528020521 : ℕ)^1045*100000000000000^789 ≤ 40523651980709^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528020521 5000000000 40523651980709 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863062469/2000000000 : ℝ), (3681693717/10000000000 : ℝ), (2528020521/5000000000 : ℝ)] ![(32853966905917/100000000000000 : ℝ), (332779763653/1250000000000 : ℝ), (40523651980709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863062469/2000000000 : ℝ)|^1045 ≤ (32853966905917/100000000000000 : ℝ)^789
        have hw : |(863062469/2000000000 : ℝ)|=(863062469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3681693717/10000000000 : ℝ)|^1045 ≤ (332779763653/1250000000000 : ℝ)^789
        have hw : |(3681693717/10000000000 : ℝ)|=(3681693717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2528020521/5000000000 : ℝ)|^1045 ≤ (40523651980709/100000000000000 : ℝ)^789
        have hw : |(2528020521/5000000000 : ℝ)|=(2528020521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s1_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-260943631/1250000000 : ℝ)*x 0 + (200669919/400000000 : ℝ)*x 1 + (2842703471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260943631/1250000000 : ℝ)^1045 ≤ (3139244215877/25000000000000 : ℝ)^789 := by
    have hnat : (260943631 : ℕ)^1045*25000000000000^789 ≤ 3139244215877^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260943631 1250000000 3139244215877 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200669919/400000000 : ℝ)^1045 ≤ (10026766573103/25000000000000 : ℝ)^789 := by
    have hnat : (200669919 : ℕ)^1045*25000000000000^789 ≤ 10026766573103^789*400000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200669919 400000000 10026766573103 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842703471/5000000000 : ℝ)^1045 ≤ (5916994604643/12500000000000 : ℝ)^789 := by
    have hnat : (2842703471 : ℕ)^1045*12500000000000^789 ≤ 5916994604643^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842703471 5000000000 5916994604643 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260943631/1250000000 : ℝ), (200669919/400000000 : ℝ), (2842703471/5000000000 : ℝ)] ![(3139244215877/25000000000000 : ℝ), (10026766573103/25000000000000 : ℝ), (5916994604643/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260943631/1250000000 : ℝ)|^1045 ≤ (3139244215877/25000000000000 : ℝ)^789
        have hw : |(-260943631/1250000000 : ℝ)|=(260943631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200669919/400000000 : ℝ)|^1045 ≤ (10026766573103/25000000000000 : ℝ)^789
        have hw : |(200669919/400000000 : ℝ)|=(200669919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842703471/5000000000 : ℝ)|^1045 ≤ (5916994604643/12500000000000 : ℝ)^789
        have hw : |(2842703471/5000000000 : ℝ)|=(2842703471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s1_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5241287373/10000000000 : ℝ)*x 0 + (-88966209/500000000 : ℝ)*x 1 + (5685409999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241287373/10000000000 : ℝ)^1045 ≤ (42501713524461/100000000000000 : ℝ)^789 := by
    have hnat : (5241287373 : ℕ)^1045*100000000000000^789 ≤ 42501713524461^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241287373 10000000000 42501713524461 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88966209/500000000 : ℝ)^1045 ≤ (10162295911677/100000000000000 : ℝ)^789 := by
    have hnat : (88966209 : ℕ)^1045*100000000000000^789 ≤ 10162295911677^789*500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88966209 500000000 10162295911677 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5685409999/10000000000 : ℝ)^1045 ≤ (2366799527379/5000000000000 : ℝ)^789 := by
    have hnat : (5685409999 : ℕ)^1045*5000000000000^789 ≤ 2366799527379^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5685409999 10000000000 2366799527379 5000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241287373/10000000000 : ℝ), (-88966209/500000000 : ℝ), (5685409999/10000000000 : ℝ)] ![(42501713524461/100000000000000 : ℝ), (10162295911677/100000000000000 : ℝ), (2366799527379/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241287373/10000000000 : ℝ)|^1045 ≤ (42501713524461/100000000000000 : ℝ)^789
        have hw : |(5241287373/10000000000 : ℝ)|=(5241287373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88966209/500000000 : ℝ)|^1045 ≤ (10162295911677/100000000000000 : ℝ)^789
        have hw : |(-88966209/500000000 : ℝ)|=(88966209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5685409999/10000000000 : ℝ)|^1045 ≤ (2366799527379/5000000000000 : ℝ)^789
        have hw : |(5685409999/10000000000 : ℝ)|=(5685409999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s1_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5241286573/10000000000 : ℝ)*x 0 + (5685411329/10000000000 : ℝ)*x 1 + (-111207711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241286573/10000000000 : ℝ)^1045 ≤ (42501704932393/100000000000000 : ℝ)^789 := by
    have hnat : (5241286573 : ℕ)^1045*100000000000000^789 ≤ 42501704932393^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241286573 10000000000 42501704932393 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5685411329/10000000000 : ℝ)^1045 ≤ (23668002606941/50000000000000 : ℝ)^789 := by
    have hnat : (5685411329 : ℕ)^1045*50000000000000^789 ≤ 23668002606941^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5685411329 10000000000 23668002606941 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111207711/625000000 : ℝ)^1045 ≤ (10162289829879/100000000000000 : ℝ)^789 := by
    have hnat : (111207711 : ℕ)^1045*100000000000000^789 ≤ 10162289829879^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111207711 625000000 10162289829879 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241286573/10000000000 : ℝ), (5685411329/10000000000 : ℝ), (-111207711/625000000 : ℝ)] ![(42501704932393/100000000000000 : ℝ), (23668002606941/50000000000000 : ℝ), (10162289829879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241286573/10000000000 : ℝ)|^1045 ≤ (42501704932393/100000000000000 : ℝ)^789
        have hw : |(5241286573/10000000000 : ℝ)|=(5241286573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5685411329/10000000000 : ℝ)|^1045 ≤ (23668002606941/50000000000000 : ℝ)^789
        have hw : |(5685411329/10000000000 : ℝ)|=(5685411329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111207711/625000000 : ℝ)|^1045 ≤ (10162289829879/100000000000000 : ℝ)^789
        have hw : |(-111207711/625000000 : ℝ)|=(111207711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s1_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (17267409/40000000 : ℝ)*x 0 + (5037456093/10000000000 : ℝ)*x 1 + (1850321931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17267409/40000000 : ℝ)^1045 ≤ (32869495564273/100000000000000 : ℝ)^789 := by
    have hnat : (17267409 : ℕ)^1045*100000000000000^789 ≤ 32869495564273^789*40000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17267409 40000000 32869495564273 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037456093/10000000000 : ℝ)^1045 ≤ (40326482644633/100000000000000 : ℝ)^789 := by
    have hnat : (5037456093 : ℕ)^1045*100000000000000^789 ≤ 40326482644633^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037456093 10000000000 40326482644633 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850321931/5000000000 : ℝ)^1045 ≤ (26804021780659/100000000000000 : ℝ)^789 := by
    have hnat : (1850321931 : ℕ)^1045*100000000000000^789 ≤ 26804021780659^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850321931 5000000000 26804021780659 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17267409/40000000 : ℝ), (5037456093/10000000000 : ℝ), (1850321931/5000000000 : ℝ)] ![(32869495564273/100000000000000 : ℝ), (40326482644633/100000000000000 : ℝ), (26804021780659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17267409/40000000 : ℝ)|^1045 ≤ (32869495564273/100000000000000 : ℝ)^789
        have hw : |(17267409/40000000 : ℝ)|=(17267409/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037456093/10000000000 : ℝ)|^1045 ≤ (40326482644633/100000000000000 : ℝ)^789
        have hw : |(5037456093/10000000000 : ℝ)|=(5037456093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1850321931/5000000000 : ℝ)|^1045 ≤ (26804021780659/100000000000000 : ℝ)^789
        have hw : |(1850321931/5000000000 : ℝ)|=(1850321931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (693/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (129/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1447/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (813/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (693/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (129/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (693/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (129/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (693/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (129/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (693/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (129/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (693/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (129/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (693/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (129/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (129/25000 : ℝ) ^ (8359/2048 : ℝ) ≤ (11535103119/25000000000000000000 : ℝ) := by
    have hpowers : (129/25000 : ℝ)^8359 ≤ (11535103119/25000000000000000000 : ℝ)^2048 := by
      have hnat : (129 : ℕ)^8359*25000000000000000000^2048 ≤ 11535103119^2048*25000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129 25000 11535103119 25000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (129/25000 : ℝ)) (X := (11535103119/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (693/2500 : ℝ) ^ (8359/2048 : ℝ) ≤ (106357128845309199/20000000000000000000 : ℝ) := by
    have hpowers : (693/2500 : ℝ)^8359 ≤ (106357128845309199/20000000000000000000 : ℝ)^2048 := by
      have hnat : (693 : ℕ)^8359*20000000000000000000^2048 ≤ 106357128845309199^2048*2500^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        693 2500 106357128845309199 20000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (693/2500 : ℝ)) (X := (106357128845309199/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000011535103119/12500000000000000000 : ℝ) ≤ (1000000000226093/1000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (12500000011535103119/12500000000000000000 : ℝ)^2048 ≤ (1000000000226093/1000000000000000 : ℝ)^8359 := by
      have hnat : (12500000011535103119 : ℕ)^2048*1000000000000000^8359 ≤ 1000000000226093^8359*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000011535103119 12500000000000000000 1000000000226093 1000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000000226093/1000000000000000 : ℝ)) (X := (12500000011535103119/12500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100531785690366958471/100000000000000000000 : ℝ) ≤ (500650148064129/500000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (100531785690366958471/100000000000000000000 : ℝ)^2048 ≤ (500650148064129/500000000000000 : ℝ)^8359 := by
      have hnat : (100531785690366958471 : ℕ)^2048*500000000000000^8359 ≤ 500650148064129^8359*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100531785690366958471 100000000000000000000 500650148064129 500000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500650148064129/500000000000000 : ℝ)) (X := (100531785690366958471/100000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10106357128845309199/10000000000000000000 : ℝ) ≤ (1002600592030423/1000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (10106357128845309199/10000000000000000000 : ℝ)^2048 ≤ (1002600592030423/1000000000000000 : ℝ)^8359 := by
      have hnat : (10106357128845309199 : ℕ)^2048*1000000000000000^8359 ≤ 1002600592030423^8359*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10106357128845309199 10000000000000000000 1002600592030423 1000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002600592030423/1000000000000000 : ℝ)) (X := (10106357128845309199/10000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11535103119/25000000000000000000 : ℝ) ≤ ((2266888175064966641/2267000000000000000 : ℝ)+2*(260059180433/54408000000000 : ℝ)*(129/25000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (2266888175064966641/2267000000000000000 : ℝ)+2*(260059180433/54408000000000 : ℝ)*(129/25000 : ℝ)=(1000000000226093/1000000000000000 : ℝ) by norm_num, show 1+2*(11535103119/25000000000000000000 : ℝ)=(12500000011535103119/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(106357128845309199/20000000000000000000 : ℝ)+(11535103119/25000000000000000000 : ℝ) ≤ ((2266888175064966641/2267000000000000000 : ℝ)+(260059180433/54408000000000 : ℝ)*((693/2500 : ℝ)+(129/25000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (2266888175064966641/2267000000000000000 : ℝ)+(260059180433/54408000000000 : ℝ)*((693/2500 : ℝ)+(129/25000 : ℝ))=(500650148064129/500000000000000 : ℝ) by norm_num, show 1+(106357128845309199/20000000000000000000 : ℝ)+(11535103119/25000000000000000000 : ℝ)=(100531785690366958471/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(106357128845309199/20000000000000000000 : ℝ) ≤ ((2266888175064966641/2267000000000000000 : ℝ)+2*(260059180433/54408000000000 : ℝ)*(693/2500 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (2266888175064966641/2267000000000000000 : ℝ)+2*(260059180433/54408000000000 : ℝ)*(693/2500 : ℝ)=(1002600592030423/1000000000000000 : ℝ) by norm_num, show 1+2*(106357128845309199/20000000000000000000 : ℝ)=(10106357128845309199/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2266888175064966641/2267000000000000000 : ℝ)*(X 1 0+X 2 0)+(260059180433/54408000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (129/25000 : ℝ)) (hi := (693/2500 : ℝ)) (c := (2266888175064966641/2267000000000000000 : ℝ)) (alpha := (260059180433/54408000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2266888175064966641/2267000000000000000 : ℝ)*(X 0 1+X 2 1)+(260059180433/54408000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (129/25000 : ℝ)) (hi := (693/2500 : ℝ)) (c := (2266888175064966641/2267000000000000000 : ℝ)) (alpha := (260059180433/54408000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2266888175064966641/2267000000000000000 : ℝ)*(X 0 2+X 1 2)+(260059180433/54408000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (129/25000 : ℝ)) (hi := (693/2500 : ℝ)) (c := (2266888175064966641/2267000000000000000 : ℝ)) (alpha := (260059180433/54408000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1043386463/5000000000 : ℝ)*X 0 0+(1423722467/2500000000 : ℝ)*X 0 1+(5007450603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541775409/1000000000 : ℝ)*X 1 0+(-1228642361/5000000000 : ℝ)*X 1 1+(5007449643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2708878103/5000000000 : ℝ)*X 2 0+(5007447693/10000000000 : ℝ)*X 2 1+(-491456889/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863062469/2000000000 : ℝ)*X 0 0+(3681693717/10000000000 : ℝ)*X 0 1+(2528020521/5000000000 : ℝ)*X 0 2+(863062469/2000000000 : ℝ)*X 1 0+(3681693717/10000000000 : ℝ)*X 1 1+(2528020521/5000000000 : ℝ)*X 1 2+(863062469/2000000000 : ℝ)*X 2 0+(3681693717/10000000000 : ℝ)*X 2 1+(2528020521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-260943631/1250000000 : ℝ)*X 0 0+(200669919/400000000 : ℝ)*X 0 1+(2842703471/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241287373/10000000000 : ℝ)*X 1 0+(-88966209/500000000 : ℝ)*X 1 1+(5685409999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5241286573/10000000000 : ℝ)*X 2 0+(5685411329/10000000000 : ℝ)*X 2 1+(-111207711/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((17267409/40000000 : ℝ)*X 0 0+(5037456093/10000000000 : ℝ)*X 0 1+(1850321931/5000000000 : ℝ)*X 0 2+(17267409/40000000 : ℝ)*X 1 0+(5037456093/10000000000 : ℝ)*X 1 1+(1850321931/5000000000 : ℝ)*X 1 2+(17267409/40000000 : ℝ)*X 2 0+(5037456093/10000000000 : ℝ)*X 2 1+(1850321931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162591750132214454598830049/28337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161083221/25000000000000 : ℝ)*(base1) + (943702657/100000000000000 : ℝ)*(base19) + (314831283/20000000000000 : ℝ)*(base23) + (135815637/50000000000000 : ℝ)*(base37) + (5716701/12500000000000 : ℝ)*(upper3) + (272786459896363/25000000000000 : ℝ)*(major0) + (272786459896363/25000000000000 : ℝ)*(major1) + (272786459896363/25000000000000 : ℝ)*(major2) + (1454674525699893/100000000000000 : ℝ)*(sp0) + (727336196839227/50000000000000 : ℝ)*(sp1) + (22729276188629/1562500000000 : ℝ)*(sp2) + (145523064344357/20000000000000 : ℝ)*(sp3) + (1368861661/100000000000000 : ℝ)*(sp4) + (47821189/2500000000000 : ℝ)*(sp5) + (727616237685943/100000000000000 : ℝ)*(f.failure) + (1454675250228671/100000000000000 : ℝ)*(f.sum) + (9001006755589/6801000000000000000000000000 : ℝ)*base66 + (241128481517955049/170025000000000000000000000000000 : ℝ)*base67 + (727291052111280049/170025000000000000000000000000000 : ℝ)*base69 + (143022113480069951/170025000000000000000000000000000 : ℝ)*base72 + (441813959933/6801000000000000000000000000 : ℝ)*base73 + (265469318164244951/170025000000000000000000000000000 : ℝ)*base76 + (422404472399969951/170025000000000000000000000000000 : ℝ)*base78 + (690138366882269951/170025000000000000000000000000000 : ℝ)*base80 + (1109945403487/340050000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (53736923/5000000000000000000000 : ℝ)*base89 + (53736923/5000000000000000000000 : ℝ)*base91 + (53736923/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47630214122436989323043217/56675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27550761/1562500000000 : ℝ)*(base19) + (2447496777/100000000000000 : ℝ)*(base23) + (369044989/100000000000000 : ℝ)*(upper2) + (262265291/50000000000000 : ℝ)*(upper3) + (120145009/50000000000000 : ℝ)*(upper5) + (1121787176828321/100000000000000 : ℝ)*(major0) + (1121787176828321/100000000000000 : ℝ)*(major1) + (1121787176828321/100000000000000 : ℝ)*(major2) + (130919/1280000000 : ℝ)*(sp1) + (2052207927/12500000000000 : ℝ)*(sp2) + (747762657812033/50000000000000 : ℝ)*(sp4) + (1495513324328487/100000000000000 : ℝ)*(sp5) + (747753225231937/50000000000000 : ℝ)*(sp6) + (748049010018917/100000000000000 : ℝ)*(sp7) + (748049010018917/100000000000000 : ℝ)*(f.failure) + (747762657812033/50000000000000 : ℝ)*(f.sum) + (51124630051601/13602000000000000000000000000 : ℝ)*base65 + (891244225678144283/680100000000000000000000000000000 : ℝ)*base67 + (849808456478644283/680100000000000000000000000000000 : ℝ)*base69 + (1494765632176144283/680100000000000000000000000000000 : ℝ)*base71 + (11142983534377/13602000000000000000000000000 : ℝ)*base74 + (2986892830502044283/680100000000000000000000000000000 : ℝ)*base75 + (1419505700206444283/680100000000000000000000000000000 : ℝ)*base77 + (2154081359590255717/680100000000000000000000000000000 : ℝ)*base80 + (1040772289909/2720400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (27052463/5000000000000000000000 : ℝ)*base90 + (27052463/5000000000000000000000 : ℝ)*base92 + (27052463/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1167_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (693/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (129/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1447/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (813/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1167_s2_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069339611/5000000000 : ℝ)*x 0 + (5506121483/10000000000 : ℝ)*x 1 + (5163188119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069339611/5000000000 : ℝ)^1045 ≤ (12965934037177/100000000000000 : ℝ)^789 := by
    have hnat : (1069339611 : ℕ)^1045*100000000000000^789 ≤ 12965934037177^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069339611 5000000000 12965934037177 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506121483/10000000000 : ℝ)^1045 ≤ (45369110609589/100000000000000 : ℝ)^789 := by
    have hnat : (5506121483 : ℕ)^1045*100000000000000^789 ≤ 45369110609589^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506121483 10000000000 45369110609589 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5163188119/10000000000 : ℝ)^1045 ≤ (5208119417607/12500000000000 : ℝ)^789 := by
    have hnat : (5163188119 : ℕ)^1045*12500000000000^789 ≤ 5208119417607^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163188119 10000000000 5208119417607 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069339611/5000000000 : ℝ), (5506121483/10000000000 : ℝ), (5163188119/10000000000 : ℝ)] ![(12965934037177/100000000000000 : ℝ), (45369110609589/100000000000000 : ℝ), (5208119417607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069339611/5000000000 : ℝ)|^1045 ≤ (12965934037177/100000000000000 : ℝ)^789
        have hw : |(-1069339611/5000000000 : ℝ)|=(1069339611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506121483/10000000000 : ℝ)|^1045 ≤ (45369110609589/100000000000000 : ℝ)^789
        have hw : |(5506121483/10000000000 : ℝ)|=(5506121483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5163188119/10000000000 : ℝ)|^1045 ≤ (5208119417607/12500000000000 : ℝ)^789
        have hw : |(5163188119/10000000000 : ℝ)|=(5163188119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s2_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5372798043/10000000000 : ℝ)*x 0 + (-579199697/2500000000 : ℝ)*x 1 + (5163190853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372798043/10000000000 : ℝ)^1045 ≤ (43919866698137/100000000000000 : ℝ)^789 := by
    have hnat : (5372798043 : ℕ)^1045*100000000000000^789 ≤ 43919866698137^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372798043 10000000000 43919866698137 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579199697/2500000000 : ℝ)^1045 ≤ (14415148725797/100000000000000 : ℝ)^789 := by
    have hnat : (579199697 : ℕ)^1045*100000000000000^789 ≤ 14415148725797^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579199697 2500000000 14415148725797 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5163190853/10000000000 : ℝ)^1045 ≤ (41664984561569/100000000000000 : ℝ)^789 := by
    have hnat : (5163190853 : ℕ)^1045*100000000000000^789 ≤ 41664984561569^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163190853 10000000000 41664984561569 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372798043/10000000000 : ℝ), (-579199697/2500000000 : ℝ), (5163190853/10000000000 : ℝ)] ![(43919866698137/100000000000000 : ℝ), (14415148725797/100000000000000 : ℝ), (41664984561569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372798043/10000000000 : ℝ)|^1045 ≤ (43919866698137/100000000000000 : ℝ)^789
        have hw : |(5372798043/10000000000 : ℝ)|=(5372798043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579199697/2500000000 : ℝ)|^1045 ≤ (14415148725797/100000000000000 : ℝ)^789
        have hw : |(-579199697/2500000000 : ℝ)|=(579199697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5163190853/10000000000 : ℝ)|^1045 ≤ (41664984561569/100000000000000 : ℝ)^789
        have hw : |(5163190853/10000000000 : ℝ)|=(5163190853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s2_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2686399261/5000000000 : ℝ)*x 0 + (5163190021/10000000000 : ℝ)*x 1 + (-1158399619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686399261/5000000000 : ℝ)^1045 ≤ (4391987188417/10000000000000 : ℝ)^789 := by
    have hnat : (2686399261 : ℕ)^1045*10000000000000^789 ≤ 4391987188417^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686399261 5000000000 4391987188417 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5163190021/10000000000 : ℝ)^1045 ≤ (41664975669237/100000000000000 : ℝ)^789 := by
    have hnat : (5163190021 : ℕ)^1045*100000000000000^789 ≤ 41664975669237^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163190021 10000000000 41664975669237 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158399619/5000000000 : ℝ)^1045 ≤ (14415152434163/100000000000000 : ℝ)^789 := by
    have hnat : (1158399619 : ℕ)^1045*100000000000000^789 ≤ 14415152434163^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158399619 5000000000 14415152434163 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686399261/5000000000 : ℝ), (5163190021/10000000000 : ℝ), (-1158399619/5000000000 : ℝ)] ![(4391987188417/10000000000000 : ℝ), (41664975669237/100000000000000 : ℝ), (14415152434163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686399261/5000000000 : ℝ)|^1045 ≤ (4391987188417/10000000000000 : ℝ)^789
        have hw : |(2686399261/5000000000 : ℝ)|=(2686399261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5163190021/10000000000 : ℝ)|^1045 ≤ (41664975669237/100000000000000 : ℝ)^789
        have hw : |(5163190021/10000000000 : ℝ)|=(5163190021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1158399619/5000000000 : ℝ)|^1045 ≤ (14415152434163/100000000000000 : ℝ)^789
        have hw : |(-1158399619/5000000000 : ℝ)|=(1158399619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s2_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4350980671/10000000000 : ℝ)*x 0 + (4021486837/10000000000 : ℝ)*x 1 + (4707086273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350980671/10000000000 : ℝ)^1045 ≤ (6642822562069/20000000000000 : ℝ)^789 := by
    have hnat : (4350980671 : ℕ)^1045*20000000000000^789 ≤ 6642822562069^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350980671 10000000000 6642822562069 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021486837/10000000000 : ℝ)^1045 ≤ (29924397357353/100000000000000 : ℝ)^789 := by
    have hnat : (4021486837 : ℕ)^1045*100000000000000^789 ≤ 29924397357353^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021486837 10000000000 29924397357353 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4707086273/10000000000 : ℝ)^1045 ≤ (18430744905867/50000000000000 : ℝ)^789 := by
    have hnat : (4707086273 : ℕ)^1045*50000000000000^789 ≤ 18430744905867^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707086273 10000000000 18430744905867 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350980671/10000000000 : ℝ), (4021486837/10000000000 : ℝ), (4707086273/10000000000 : ℝ)] ![(6642822562069/20000000000000 : ℝ), (29924397357353/100000000000000 : ℝ), (18430744905867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350980671/10000000000 : ℝ)|^1045 ≤ (6642822562069/20000000000000 : ℝ)^789
        have hw : |(4350980671/10000000000 : ℝ)|=(4350980671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4021486837/10000000000 : ℝ)|^1045 ≤ (29924397357353/100000000000000 : ℝ)^789
        have hw : |(4021486837/10000000000 : ℝ)|=(4021486837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4707086273/10000000000 : ℝ)|^1045 ≤ (18430744905867/50000000000000 : ℝ)^789
        have hw : |(4707086273/10000000000 : ℝ)|=(4707086273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s2_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138774487/10000000000 : ℝ)*x 0 + (5165512519/10000000000 : ℝ)*x 1 + (85996479/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138774487/10000000000 : ℝ)^1045 ≤ (12966698988773/100000000000000 : ℝ)^789 := by
    have hnat : (2138774487 : ℕ)^1045*100000000000000^789 ≤ 12966698988773^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138774487 10000000000 12966698988773 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5165512519/10000000000 : ℝ)^1045 ≤ (20844900051403/50000000000000 : ℝ)^789 := by
    have hnat : (5165512519 : ℕ)^1045*50000000000000^789 ≤ 20844900051403^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165512519 10000000000 20844900051403 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85996479/156250000 : ℝ)^1045 ≤ (22671750445503/50000000000000 : ℝ)^789 := by
    have hnat : (85996479 : ℕ)^1045*50000000000000^789 ≤ 22671750445503^789*156250000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85996479 156250000 22671750445503 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138774487/10000000000 : ℝ), (5165512519/10000000000 : ℝ), (85996479/156250000 : ℝ)] ![(12966698988773/100000000000000 : ℝ), (20844900051403/50000000000000 : ℝ), (22671750445503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138774487/10000000000 : ℝ)|^1045 ≤ (12966698988773/100000000000000 : ℝ)^789
        have hw : |(-2138774487/10000000000 : ℝ)|=(2138774487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5165512519/10000000000 : ℝ)|^1045 ≤ (20844900051403/50000000000000 : ℝ)^789
        have hw : |(5165512519/10000000000 : ℝ)|=(5165512519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85996479/156250000 : ℝ)|^1045 ≤ (22671750445503/50000000000000 : ℝ)^789
        have hw : |(85996479/156250000 : ℝ)|=(85996479/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s2_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1321410681/2500000000 : ℝ)*x 0 + (-1976213837/10000000000 : ℝ)*x 1 + (1375943663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321410681/2500000000 : ℝ)^1045 ≤ (42978746587907/100000000000000 : ℝ)^789 := by
    have hnat : (1321410681 : ℕ)^1045*100000000000000^789 ≤ 42978746587907^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321410681 2500000000 42978746587907 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976213837/10000000000 : ℝ)^1045 ≤ (467110102227/4000000000000 : ℝ)^789 := by
    have hnat : (1976213837 : ℕ)^1045*4000000000000^789 ≤ 467110102227^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976213837 10000000000 467110102227 4000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375943663/2500000000 : ℝ)^1045 ≤ (45343500847359/100000000000000 : ℝ)^789 := by
    have hnat : (1375943663 : ℕ)^1045*100000000000000^789 ≤ 45343500847359^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375943663 2500000000 45343500847359 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321410681/2500000000 : ℝ), (-1976213837/10000000000 : ℝ), (1375943663/2500000000 : ℝ)] ![(42978746587907/100000000000000 : ℝ), (467110102227/4000000000000 : ℝ), (45343500847359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321410681/2500000000 : ℝ)|^1045 ≤ (42978746587907/100000000000000 : ℝ)^789
        have hw : |(1321410681/2500000000 : ℝ)|=(1321410681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1976213837/10000000000 : ℝ)|^1045 ≤ (467110102227/4000000000000 : ℝ)^789
        have hw : |(-1976213837/10000000000 : ℝ)|=(1976213837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1375943663/2500000000 : ℝ)|^1045 ≤ (45343500847359/100000000000000 : ℝ)^789
        have hw : |(1375943663/2500000000 : ℝ)|=(1375943663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s2_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5285642851/10000000000 : ℝ)*x 0 + (687971831/1250000000 : ℝ)*x 1 + (-494053417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285642851/10000000000 : ℝ)^1045 ≤ (42978747955633/100000000000000 : ℝ)^789 := by
    have hnat : (5285642851 : ℕ)^1045*100000000000000^789 ≤ 42978747955633^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285642851 10000000000 42978747955633 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687971831/1250000000 : ℝ)^1045 ≤ (354246100029/781250000000 : ℝ)^789 := by
    have hnat : (687971831 : ℕ)^1045*781250000000^789 ≤ 354246100029^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687971831 1250000000 354246100029 781250000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494053417/2500000000 : ℝ)^1045 ≤ (2335550246601/20000000000000 : ℝ)^789 := by
    have hnat : (494053417 : ℕ)^1045*20000000000000^789 ≤ 2335550246601^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494053417 2500000000 2335550246601 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285642851/10000000000 : ℝ), (687971831/1250000000 : ℝ), (-494053417/2500000000 : ℝ)] ![(42978747955633/100000000000000 : ℝ), (354246100029/781250000000 : ℝ), (2335550246601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285642851/10000000000 : ℝ)|^1045 ≤ (42978747955633/100000000000000 : ℝ)^789
        have hw : |(5285642851/10000000000 : ℝ)|=(5285642851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687971831/1250000000 : ℝ)|^1045 ≤ (354246100029/781250000000 : ℝ)^789
        have hw : |(687971831/1250000000 : ℝ)|=(687971831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494053417/2500000000 : ℝ)|^1045 ≤ (2335550246601/20000000000000 : ℝ)^789
        have hw : |(-494053417/2500000000 : ℝ)|=(494053417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s2_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4351172753/10000000000 : ℝ)*x 0 + (146951303/312500000 : ℝ)*x 1 + (4026176079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351172753/10000000000 : ℝ)^1045 ≤ (8304013719739/25000000000000 : ℝ)^789 := by
    have hnat : (4351172753 : ℕ)^1045*25000000000000^789 ≤ 8304013719739^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351172753 10000000000 8304013719739 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146951303/312500000 : ℝ)^1045 ≤ (36813324248983/100000000000000 : ℝ)^789 := by
    have hnat : (146951303 : ℕ)^1045*100000000000000^789 ≤ 36813324248983^789*312500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146951303 312500000 36813324248983 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4026176079/10000000000 : ℝ)^1045 ≤ (7492655214169/25000000000000 : ℝ)^789 := by
    have hnat : (4026176079 : ℕ)^1045*25000000000000^789 ≤ 7492655214169^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026176079 10000000000 7492655214169 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351172753/10000000000 : ℝ), (146951303/312500000 : ℝ), (4026176079/10000000000 : ℝ)] ![(8304013719739/25000000000000 : ℝ), (36813324248983/100000000000000 : ℝ), (7492655214169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351172753/10000000000 : ℝ)|^1045 ≤ (8304013719739/25000000000000 : ℝ)^789
        have hw : |(4351172753/10000000000 : ℝ)|=(4351172753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146951303/312500000 : ℝ)|^1045 ≤ (36813324248983/100000000000000 : ℝ)^789
        have hw : |(146951303/312500000 : ℝ)|=(146951303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4026176079/10000000000 : ℝ)|^1045 ≤ (7492655214169/25000000000000 : ℝ)^789
        have hw : |(4026176079/10000000000 : ℝ)|=(4026176079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1447/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4591/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16429/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (813/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1447/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (813/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1447/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (813/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1447/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (813/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1447/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (813/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1447/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (813/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1447/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1447/25000 : ℝ) ^ (8359/2048 : ℝ) ≤ (222406256621521/25000000000000000000 : ℝ) := by
    have hpowers : (1447/25000 : ℝ)^8359 ≤ (222406256621521/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1447 : ℕ)^8359*25000000000000000000^2048 ≤ 222406256621521^2048*25000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1447 25000 222406256621521 25000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1447/25000 : ℝ)) (X := (222406256621521/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (813/4000 : ℝ) ^ (8359/2048 : ℝ) ≤ (74931940312851049/50000000000000000000 : ℝ) := by
    have hpowers : (813/4000 : ℝ)^8359 ≤ (74931940312851049/50000000000000000000 : ℝ)^2048 := by
      have hnat : (813 : ℕ)^8359*50000000000000000000^2048 ≤ 74931940312851049^2048*4000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        813 4000 74931940312851049 50000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (813/4000 : ℝ)) (X := (74931940312851049/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500222406256621521/12500000000000000000 : ℝ) ≤ (10000043592291351/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (12500222406256621521/12500000000000000000 : ℝ)^2048 ≤ (10000043592291351/10000000000000000 : ℝ)^8359 := by
      have hnat : (12500222406256621521 : ℕ)^2048*10000000000000000^8359 ≤ 10000043592291351^8359*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500222406256621521 12500000000000000000 10000043592291351 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000043592291351/10000000000000000 : ℝ)) (X := (12500222406256621521/12500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50075376752826094091/50000000000000000000 : ℝ) ≤ (10003691441937799/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (50075376752826094091/50000000000000000000 : ℝ)^2048 ≤ (10003691441937799/10000000000000000 : ℝ)^8359 := by
      have hnat : (50075376752826094091 : ℕ)^2048*10000000000000000^8359 ≤ 10003691441937799^8359*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075376752826094091 50000000000000000000 10003691441937799 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003691441937799/10000000000000000 : ℝ)) (X := (50075376752826094091/50000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25074931940312851049/25000000000000000000 : ℝ) ≤ (10007339291584247/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (25074931940312851049/25000000000000000000 : ℝ)^2048 ≤ (10007339291584247/10000000000000000 : ℝ)^8359 := by
      have hnat : (25074931940312851049 : ℕ)^2048*10000000000000000^8359 ≤ 10007339291584247^8359*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25074931940312851049 25000000000000000000 10007339291584247 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007339291584247/10000000000000000 : ℝ)) (X := (25074931940312851049/25000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(222406256621521/25000000000000000000 : ℝ) ≤ ((145328406193632087439/145370000000000000000 : ℝ)+2*(227990602903/90856250000000 : ℝ)*(1447/25000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (145328406193632087439/145370000000000000000 : ℝ)+2*(227990602903/90856250000000 : ℝ)*(1447/25000 : ℝ)=(10000043592291351/10000000000000000 : ℝ) by norm_num, show 1+2*(222406256621521/25000000000000000000 : ℝ)=(12500222406256621521/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74931940312851049/50000000000000000000 : ℝ)+(222406256621521/25000000000000000000 : ℝ) ≤ ((145328406193632087439/145370000000000000000 : ℝ)+(227990602903/90856250000000 : ℝ)*((813/4000 : ℝ)+(1447/25000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (145328406193632087439/145370000000000000000 : ℝ)+(227990602903/90856250000000 : ℝ)*((813/4000 : ℝ)+(1447/25000 : ℝ))=(10003691441937799/10000000000000000 : ℝ) by norm_num, show 1+(74931940312851049/50000000000000000000 : ℝ)+(222406256621521/25000000000000000000 : ℝ)=(50075376752826094091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74931940312851049/50000000000000000000 : ℝ) ≤ ((145328406193632087439/145370000000000000000 : ℝ)+2*(227990602903/90856250000000 : ℝ)*(813/4000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (145328406193632087439/145370000000000000000 : ℝ)+2*(227990602903/90856250000000 : ℝ)*(813/4000 : ℝ)=(10007339291584247/10000000000000000 : ℝ) by norm_num, show 1+2*(74931940312851049/50000000000000000000 : ℝ)=(25074931940312851049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (145328406193632087439/145370000000000000000 : ℝ)*(X 1 0+X 2 0)+(227990602903/90856250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (1447/25000 : ℝ)) (hi := (813/4000 : ℝ)) (c := (145328406193632087439/145370000000000000000 : ℝ)) (alpha := (227990602903/90856250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (145328406193632087439/145370000000000000000 : ℝ)*(X 0 1+X 2 1)+(227990602903/90856250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (1447/25000 : ℝ)) (hi := (813/4000 : ℝ)) (c := (145328406193632087439/145370000000000000000 : ℝ)) (alpha := (227990602903/90856250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (145328406193632087439/145370000000000000000 : ℝ)*(X 0 2+X 1 2)+(227990602903/90856250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (1447/25000 : ℝ)) (hi := (813/4000 : ℝ)) (c := (145328406193632087439/145370000000000000000 : ℝ)) (alpha := (227990602903/90856250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1069339611/5000000000 : ℝ)*X 0 0+(5506121483/10000000000 : ℝ)*X 0 1+(5163188119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372798043/10000000000 : ℝ)*X 1 0+(-579199697/2500000000 : ℝ)*X 1 1+(5163190853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686399261/5000000000 : ℝ)*X 2 0+(5163190021/10000000000 : ℝ)*X 2 1+(-1158399619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350980671/10000000000 : ℝ)*X 0 0+(4021486837/10000000000 : ℝ)*X 0 1+(4707086273/10000000000 : ℝ)*X 0 2+(4350980671/10000000000 : ℝ)*X 1 0+(4021486837/10000000000 : ℝ)*X 1 1+(4707086273/10000000000 : ℝ)*X 1 2+(4350980671/10000000000 : ℝ)*X 2 0+(4021486837/10000000000 : ℝ)*X 2 1+(4707086273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2138774487/10000000000 : ℝ)*X 0 0+(5165512519/10000000000 : ℝ)*X 0 1+(85996479/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321410681/2500000000 : ℝ)*X 1 0+(-1976213837/10000000000 : ℝ)*X 1 1+(1375943663/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285642851/10000000000 : ℝ)*X 2 0+(687971831/1250000000 : ℝ)*X 2 1+(-494053417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351172753/10000000000 : ℝ)*X 0 0+(146951303/312500000 : ℝ)*X 0 1+(4026176079/10000000000 : ℝ)*X 0 2+(4351172753/10000000000 : ℝ)*X 1 0+(146951303/312500000 : ℝ)*X 1 1+(4026176079/10000000000 : ℝ)*X 1 2+(4351172753/10000000000 : ℝ)*X 2 0+(146951303/312500000 : ℝ)*X 2 1+(4026176079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8797589961444429597506374509/1817125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52008827/50000000000000 : ℝ)*(base19) + (152698071/50000000000000 : ℝ)*(base23) + (53924567/50000000000000 : ℝ)*(upper2) + (56073093/20000000000000 : ℝ)*(upper3) + (69665789/50000000000000 : ℝ)*(upper4) + (546830211764459/25000000000000 : ℝ)*(major0) + (546830211764459/25000000000000 : ℝ)*(major1) + (546830211764459/25000000000000 : ℝ)*(major2) + (729009692369237/25000000000000 : ℝ)*(sp0) + (1458027659474551/50000000000000 : ℝ)*(sp1) + (1458027558785307/50000000000000 : ℝ)*(sp2) + (729290201371083/50000000000000 : ℝ)*(sp3) + (1040843113/6250000000000 : ℝ)*(sp4) + (570702379/10000000000000 : ℝ)*(sp7) + (291717221953191/20000000000000 : ℝ)*(f.failure) + (729013855741689/25000000000000 : ℝ)*(f.sum) + (19143737654357/4542812500000000000000000000 : ℝ)*base66 + (20342733876942769499/3634250000000000000000000000000000 : ℝ)*base68 + (49893535011465269499/3634250000000000000000000000000000 : ℝ)*base70 + (13766113756964769499/3634250000000000000000000000000000 : ℝ)*base72 + (95494854611791/36342500000000000000000000000 : ℝ)*base74 + (28219875229315769499/3634250000000000000000000000000000 : ℝ)*base76 + (68598315356593269499/3634250000000000000000000000000000 : ℝ)*base78 + (19065886141779269499/3634250000000000000000000000000000 : ℝ)*base80 + (71477011735933/18171250000000000000000000000 : ℝ)*base82 + (2877451/1000000000000000000000 : ℝ)*base89 + (2877451/1000000000000000000000 : ℝ)*base91 + (2877451/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5146824266821289645751210369/1453700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1845483/200000000000 : ℝ)*(base19) + (1073197889/100000000000000 : ℝ)*(base23) + (400217/2000000000000 : ℝ)*(upper2) + (14587737/12500000000000 : ℝ)*(upper3) + (79532507/100000000000000 : ℝ)*(upper5) + (443499609423319/20000000000000 : ℝ)*(major0) + (443499609423319/20000000000000 : ℝ)*(major1) + (443499609423319/20000000000000 : ℝ)*(major2) + (2180087263/25000000000000 : ℝ)*(sp1) + (5620556579/50000000000000 : ℝ)*(sp2) + (1478143298944121/50000000000000 : ℝ)*(sp4) + (295627695479769/10000000000000 : ℝ)*(sp5) + (591254856715439/20000000000000 : ℝ)*(sp6) + (46209668072759/3125000000000 : ℝ)*(sp7) + (46209668072759/3125000000000 : ℝ)*(f.failure) + (1478143298944121/50000000000000 : ℝ)*(f.sum) + (8500404220271/7268500000000000000000000000 : ℝ)*base65 + (33204759553875609959/2907400000000000000000000000000000 : ℝ)*base68 + (21809843306064809959/2907400000000000000000000000000000 : ℝ)*base70 + (22451309236419209959/2907400000000000000000000000000000 : ℝ)*base72 + (4404497221471/7268500000000000000000000000 : ℝ)*base74 + (41649302685246409959/2907400000000000000000000000000000 : ℝ)*base76 + (23883269516344209959/2907400000000000000000000000000000 : ℝ)*base78 + (27085982394267609959/2907400000000000000000000000000000 : ℝ)*base80 + (818157108533/454281250000000000000000000 : ℝ)*base81 + (777999/156250000000000000000 : ℝ)*base89 + (777999/156250000000000000000 : ℝ)*base91 + (777999/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1167_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1447/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16429/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1167_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16429/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1167_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1167_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1167_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16429/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
