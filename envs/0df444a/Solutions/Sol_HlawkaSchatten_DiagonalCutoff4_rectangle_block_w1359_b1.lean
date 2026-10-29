-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1359_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:03.86419+00:00
-- url     : https://prove2.me/submissions/ca6266e9-7911-4eb3-92aa-2449b021a56b

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
theorem support_rectangle_w1359_s3_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013891219/5000000000 : ℝ)*x 0 + (1085008531/2000000000 : ℝ)*x 1 + (5232949653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013891219/5000000000 : ℝ)^4319 ≤ (12349849984459/100000000000000 : ℝ)^3295 := by
    have hnat : (1013891219 : ℕ)^4319*100000000000000^3295 ≤ 12349849984459^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013891219 5000000000 12349849984459 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085008531/2000000000 : ℝ)^4319 ≤ (22430171538793/50000000000000 : ℝ)^3295 := by
    have hnat : (1085008531 : ℕ)^4319*50000000000000^3295 ≤ 22430171538793^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085008531 2000000000 22430171538793 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232949653/10000000000 : ℝ)^4319 ≤ (42789806919129/100000000000000 : ℝ)^3295 := by
    have hnat : (5232949653 : ℕ)^4319*100000000000000^3295 ≤ 42789806919129^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232949653 10000000000 42789806919129 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013891219/5000000000 : ℝ), (1085008531/2000000000 : ℝ), (5232949653/10000000000 : ℝ)] ![(12349849984459/100000000000000 : ℝ), (22430171538793/50000000000000 : ℝ), (42789806919129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013891219/5000000000 : ℝ)|^4319 ≤ (12349849984459/100000000000000 : ℝ)^3295
        have hw : |(-1013891219/5000000000 : ℝ)|=(1013891219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085008531/2000000000 : ℝ)|^4319 ≤ (22430171538793/50000000000000 : ℝ)^3295
        have hw : |(1085008531/2000000000 : ℝ)|=(1085008531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232949653/10000000000 : ℝ)|^4319 ≤ (42789806919129/100000000000000 : ℝ)^3295
        have hw : |(5232949653/10000000000 : ℝ)|=(5232949653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s3_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352076353/10000000000 : ℝ)*x 0 + (-1062957397/5000000000 : ℝ)*x 1 + (209317983/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352076353/10000000000 : ℝ)^4319 ≤ (110177807481/250000000000 : ℝ)^3295 := by
    have hnat : (5352076353 : ℕ)^4319*250000000000^3295 ≤ 110177807481^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352076353 10000000000 110177807481 250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062957397/5000000000 : ℝ)^4319 ≤ (13139070918967/100000000000000 : ℝ)^3295 := by
    have hnat : (1062957397 : ℕ)^4319*100000000000000^3295 ≤ 13139070918967^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062957397 5000000000 13139070918967 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209317983/400000000 : ℝ)^4319 ≤ (4278980608311/10000000000000 : ℝ)^3295 := by
    have hnat : (209317983 : ℕ)^4319*10000000000000^3295 ≤ 4278980608311^3295*400000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209317983 400000000 4278980608311 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352076353/10000000000 : ℝ), (-1062957397/5000000000 : ℝ), (209317983/400000000 : ℝ)] ![(110177807481/250000000000 : ℝ), (13139070918967/100000000000000 : ℝ), (4278980608311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352076353/10000000000 : ℝ)|^4319 ≤ (110177807481/250000000000 : ℝ)^3295
        have hw : |(5352076353/10000000000 : ℝ)|=(5352076353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062957397/5000000000 : ℝ)|^4319 ≤ (13139070918967/100000000000000 : ℝ)^3295
        have hw : |(-1062957397/5000000000 : ℝ)|=(1062957397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209317983/400000000 : ℝ)|^4319 ≤ (4278980608311/10000000000000 : ℝ)^3295
        have hw : |(209317983/400000000 : ℝ)|=(209317983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s3_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338019061/2500000000 : ℝ)*x 0 + (1308237433/2500000000 : ℝ)*x 1 + (-212591473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338019061/2500000000 : ℝ)^4319 ≤ (8814224363183/20000000000000 : ℝ)^3295 := by
    have hnat : (1338019061 : ℕ)^4319*20000000000000^3295 ≤ 8814224363183^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338019061 2500000000 8814224363183 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308237433/2500000000 : ℝ)^4319 ≤ (21394903882933/50000000000000 : ℝ)^3295 := by
    have hnat : (1308237433 : ℕ)^4319*50000000000000^3295 ≤ 21394903882933^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308237433 2500000000 21394903882933 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212591473/1000000000 : ℝ)^4319 ≤ (6569535200247/50000000000000 : ℝ)^3295 := by
    have hnat : (212591473 : ℕ)^4319*50000000000000^3295 ≤ 6569535200247^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212591473 1000000000 6569535200247 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338019061/2500000000 : ℝ), (1308237433/2500000000 : ℝ), (-212591473/1000000000 : ℝ)] ![(8814224363183/20000000000000 : ℝ), (21394903882933/50000000000000 : ℝ), (6569535200247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338019061/2500000000 : ℝ)|^4319 ≤ (8814224363183/20000000000000 : ℝ)^3295
        have hw : |(1338019061/2500000000 : ℝ)|=(1338019061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308237433/2500000000 : ℝ)|^4319 ≤ (21394903882933/50000000000000 : ℝ)^3295
        have hw : |(1308237433/2500000000 : ℝ)|=(1308237433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212591473/1000000000 : ℝ)|^4319 ≤ (6569535200247/50000000000000 : ℝ)^3295
        have hw : |(-212591473/1000000000 : ℝ)|=(212591473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s3_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540153517/1250000000 : ℝ)*x 0 + (412316131/1000000000 : ℝ)*x 1 + (2264044643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540153517/1250000000 : ℝ)^4319 ≤ (33293804276901/100000000000000 : ℝ)^3295 := by
    have hnat : (540153517 : ℕ)^4319*100000000000000^3295 ≤ 33293804276901^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540153517 1250000000 33293804276901 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412316131/1000000000 : ℝ)^4319 ≤ (61148244423/195312500000 : ℝ)^3295 := by
    have hnat : (412316131 : ℕ)^4319*195312500000^3295 ≤ 61148244423^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412316131 1000000000 61148244423 195312500000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264044643/5000000000 : ℝ)^4319 ≤ (1769914727883/5000000000000 : ℝ)^3295 := by
    have hnat : (2264044643 : ℕ)^4319*5000000000000^3295 ≤ 1769914727883^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264044643 5000000000 1769914727883 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540153517/1250000000 : ℝ), (412316131/1000000000 : ℝ), (2264044643/5000000000 : ℝ)] ![(33293804276901/100000000000000 : ℝ), (61148244423/195312500000 : ℝ), (1769914727883/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540153517/1250000000 : ℝ)|^4319 ≤ (33293804276901/100000000000000 : ℝ)^3295
        have hw : |(540153517/1250000000 : ℝ)|=(540153517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412316131/1000000000 : ℝ)|^4319 ≤ (61148244423/195312500000 : ℝ)^3295
        have hw : |(412316131/1000000000 : ℝ)|=(412316131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264044643/5000000000 : ℝ)|^4319 ≤ (1769914727883/5000000000000 : ℝ)^3295
        have hw : |(2264044643/5000000000 : ℝ)|=(2264044643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s3_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-405560147/2000000000 : ℝ)*x 0 + (5233742411/10000000000 : ℝ)*x 1 + (5424245217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405560147/2000000000 : ℝ)^4319 ≤ (12349996050281/100000000000000 : ℝ)^3295 := by
    have hnat : (405560147 : ℕ)^4319*100000000000000^3295 ≤ 12349996050281^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405560147 2000000000 12349996050281 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233742411/10000000000 : ℝ)^4319 ≤ (21399152026023/50000000000000 : ℝ)^3295 := by
    have hnat : (5233742411 : ℕ)^4319*50000000000000^3295 ≤ 21399152026023^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233742411 10000000000 21399152026023 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424245217/10000000000 : ℝ)^4319 ≤ (44851699884291/100000000000000 : ℝ)^3295 := by
    have hnat : (5424245217 : ℕ)^4319*100000000000000^3295 ≤ 44851699884291^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424245217 10000000000 44851699884291 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405560147/2000000000 : ℝ), (5233742411/10000000000 : ℝ), (5424245217/10000000000 : ℝ)] ![(12349996050281/100000000000000 : ℝ), (21399152026023/50000000000000 : ℝ), (44851699884291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405560147/2000000000 : ℝ)|^4319 ≤ (12349996050281/100000000000000 : ℝ)^3295
        have hw : |(-405560147/2000000000 : ℝ)|=(405560147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233742411/10000000000 : ℝ)|^4319 ≤ (21399152026023/50000000000000 : ℝ)^3295
        have hw : |(5233742411/10000000000 : ℝ)|=(5233742411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424245217/10000000000 : ℝ)|^4319 ≤ (44851699884291/100000000000000 : ℝ)^3295
        have hw : |(5424245217/10000000000 : ℝ)|=(5424245217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s3_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302501233/10000000000 : ℝ)*x 0 + (-483654801/2500000000 : ℝ)*x 1 + (542424521/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302501233/10000000000 : ℝ)^4319 ≤ (21768404528347/50000000000000 : ℝ)^3295 := by
    have hnat : (5302501233 : ℕ)^4319*50000000000000^3295 ≤ 21768404528347^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302501233 10000000000 21768404528347 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483654801/2500000000 : ℝ)^4319 ≤ (11611491113401/100000000000000 : ℝ)^3295 := by
    have hnat : (483654801 : ℕ)^4319*100000000000000^3295 ≤ 11611491113401^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483654801 2500000000 11611491113401 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542424521/1000000000 : ℝ)^4319 ≤ (22425849904211/50000000000000 : ℝ)^3295 := by
    have hnat : (542424521 : ℕ)^4319*50000000000000^3295 ≤ 22425849904211^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542424521 1000000000 22425849904211 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302501233/10000000000 : ℝ), (-483654801/2500000000 : ℝ), (542424521/1000000000 : ℝ)] ![(21768404528347/50000000000000 : ℝ), (11611491113401/100000000000000 : ℝ), (22425849904211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302501233/10000000000 : ℝ)|^4319 ≤ (21768404528347/50000000000000 : ℝ)^3295
        have hw : |(5302501233/10000000000 : ℝ)|=(5302501233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-483654801/2500000000 : ℝ)|^4319 ≤ (11611491113401/100000000000000 : ℝ)^3295
        have hw : |(-483654801/2500000000 : ℝ)|=(483654801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542424521/1000000000 : ℝ)|^4319 ≤ (22425849904211/50000000000000 : ℝ)^3295
        have hw : |(542424521/1000000000 : ℝ)|=(542424521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s3_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325625271/2500000000 : ℝ)*x 0 + (1084849063/2000000000 : ℝ)*x 1 + (-15114213/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325625271/2500000000 : ℝ)^4319 ≤ (43536807453117/100000000000000 : ℝ)^3295 := by
    have hnat : (1325625271 : ℕ)^4319*100000000000000^3295 ≤ 43536807453117^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325625271 2500000000 43536807453117 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084849063/2000000000 : ℝ)^4319 ≤ (2242585047323/5000000000000 : ℝ)^3295 := by
    have hnat : (1084849063 : ℕ)^4319*5000000000000^3295 ≤ 2242585047323^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084849063 2000000000 2242585047323 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15114213/78125000 : ℝ)^4319 ≤ (11611491585433/100000000000000 : ℝ)^3295 := by
    have hnat : (15114213 : ℕ)^4319*100000000000000^3295 ≤ 11611491585433^3295*78125000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15114213 78125000 11611491585433 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325625271/2500000000 : ℝ), (1084849063/2000000000 : ℝ), (-15114213/78125000 : ℝ)] ![(43536807453117/100000000000000 : ℝ), (2242585047323/5000000000000 : ℝ), (11611491585433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325625271/2500000000 : ℝ)|^4319 ≤ (43536807453117/100000000000000 : ℝ)^3295
        have hw : |(1325625271/2500000000 : ℝ)|=(1325625271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084849063/2000000000 : ℝ)|^4319 ≤ (2242585047323/5000000000000 : ℝ)^3295
        have hw : |(1084849063/2000000000 : ℝ)|=(1084849063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15114213/78125000 : ℝ)|^4319 ≤ (11611491585433/100000000000000 : ℝ)^3295
        have hw : |(-15114213/78125000 : ℝ)|=(15114213/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s3_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080316711/2500000000 : ℝ)*x 0 + (565802249/1250000000 : ℝ)*x 1 + (824968499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080316711/2500000000 : ℝ)^4319 ≤ (16647097597307/50000000000000 : ℝ)^3295 := by
    have hnat : (1080316711 : ℕ)^4319*50000000000000^3295 ≤ 16647097597307^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080316711 2500000000 16647097597307 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565802249/1250000000 : ℝ)^4319 ≤ (17690584926593/50000000000000 : ℝ)^3295 := by
    have hnat : (565802249 : ℕ)^4319*50000000000000^3295 ≤ 17690584926593^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565802249 1250000000 17690584926593 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824968499/2000000000 : ℝ)^4319 ≤ (31324634939099/100000000000000 : ℝ)^3295 := by
    have hnat : (824968499 : ℕ)^4319*100000000000000^3295 ≤ 31324634939099^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824968499 2000000000 31324634939099 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080316711/2500000000 : ℝ), (565802249/1250000000 : ℝ), (824968499/2000000000 : ℝ)] ![(16647097597307/50000000000000 : ℝ), (17690584926593/50000000000000 : ℝ), (31324634939099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080316711/2500000000 : ℝ)|^4319 ≤ (16647097597307/50000000000000 : ℝ)^3295
        have hw : |(1080316711/2500000000 : ℝ)|=(1080316711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565802249/1250000000 : ℝ)|^4319 ≤ (17690584926593/50000000000000 : ℝ)^3295
        have hw : |(565802249/1250000000 : ℝ)|=(565802249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(824968499/2000000000 : ℝ)|^4319 ≤ (31324634939099/100000000000000 : ℝ)^3295
        have hw : |(824968499/2000000000 : ℝ)|=(824968499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (683/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7497/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9961/100000 : ℝ) ^ (2159/512 : ℝ) ≤ (5970998582905077/100000000000000000000 : ℝ) := by
    have hpowers : (9961/100000 : ℝ)^2159 ≤ (5970998582905077/100000000000000000000 : ℝ)^512 := by
      have hnat : (9961 : ℕ)^2159*100000000000000000000^512 ≤ 5970998582905077^512*100000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9961 100000 5970998582905077 100000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9961/100000 : ℝ)) (X := (5970998582905077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8019/50000 : ℝ) ^ (2159/512 : ℝ) ≤ (8898358145703797/20000000000000000000 : ℝ) := by
    have hpowers : (8019/50000 : ℝ)^2159 ≤ (8898358145703797/20000000000000000000 : ℝ)^512 := by
      have hnat : (8019 : ℕ)^2159*20000000000000000000^512 ≤ 8898358145703797^512*50000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8019 50000 8898358145703797 20000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8019/50000 : ℝ)) (X := (8898358145703797/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005970998582905077/50000000000000000000 : ℝ) ≤ (400011327511/400000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (50005970998582905077/50000000000000000000 : ℝ)^512 ≤ (400011327511/400000000000 : ℝ)^2159 := by
      have hnat : (50005970998582905077 : ℕ)^512*400000000000^2159 ≤ 400011327511^2159*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005970998582905077 50000000000000000000 400011327511 400000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400011327511/400000000000 : ℝ)) (X := (50005970998582905077/50000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025231394655712031/50000000000000000000 : ℝ) ≤ (10001196478765387/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (50025231394655712031/50000000000000000000 : ℝ)^512 ≤ (10001196478765387/10000000000000000 : ℝ)^2159 := by
      have hnat : (50025231394655712031 : ℕ)^512*10000000000000000^2159 ≤ 10001196478765387^2159*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025231394655712031 50000000000000000000 10001196478765387 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001196478765387/10000000000000000 : ℝ)) (X := (50025231394655712031/50000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008898358145703797/10000000000000000000 : ℝ) ≤ (5001054884877887/5000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (10008898358145703797/10000000000000000000 : ℝ)^512 ≤ (5001054884877887/5000000000000000 : ℝ)^2159 := by
      have hnat : (10008898358145703797 : ℕ)^512*5000000000000000^2159 ≤ 5001054884877887^2159*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008898358145703797 10000000000000000000 5001054884877887 5000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001054884877887/5000000000000000 : ℝ)) (X := (10008898358145703797/10000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5970998582905077/100000000000000000000 : ℝ) ≤ ((30376763174499092593/30385000000000000000 : ℝ)+2*(913290990387/607700000000000 : ℝ)*(9961/100000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (30376763174499092593/30385000000000000000 : ℝ)+2*(913290990387/607700000000000 : ℝ)*(9961/100000 : ℝ)=(400011327511/400000000000 : ℝ) by norm_num, show 1+2*(5970998582905077/100000000000000000000 : ℝ)=(50005970998582905077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8898358145703797/20000000000000000000 : ℝ)+(5970998582905077/100000000000000000000 : ℝ) ≤ ((30376763174499092593/30385000000000000000 : ℝ)+(913290990387/607700000000000 : ℝ)*((8019/50000 : ℝ)+(9961/100000 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (30376763174499092593/30385000000000000000 : ℝ)+(913290990387/607700000000000 : ℝ)*((8019/50000 : ℝ)+(9961/100000 : ℝ))=(10001196478765387/10000000000000000 : ℝ) by norm_num, show 1+(8898358145703797/20000000000000000000 : ℝ)+(5970998582905077/100000000000000000000 : ℝ)=(50025231394655712031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8898358145703797/20000000000000000000 : ℝ) ≤ ((30376763174499092593/30385000000000000000 : ℝ)+2*(913290990387/607700000000000 : ℝ)*(8019/50000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (30376763174499092593/30385000000000000000 : ℝ)+2*(913290990387/607700000000000 : ℝ)*(8019/50000 : ℝ)=(5001054884877887/5000000000000000 : ℝ) by norm_num, show 1+2*(8898358145703797/20000000000000000000 : ℝ)=(10008898358145703797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30376763174499092593/30385000000000000000 : ℝ)*(X 1 0+X 2 0)+(913290990387/607700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (8019/50000 : ℝ)) (c := (30376763174499092593/30385000000000000000 : ℝ)) (alpha := (913290990387/607700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30376763174499092593/30385000000000000000 : ℝ)*(X 0 1+X 2 1)+(913290990387/607700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (8019/50000 : ℝ)) (c := (30376763174499092593/30385000000000000000 : ℝ)) (alpha := (913290990387/607700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30376763174499092593/30385000000000000000 : ℝ)*(X 0 2+X 1 2)+(913290990387/607700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (8019/50000 : ℝ)) (c := (30376763174499092593/30385000000000000000 : ℝ)) (alpha := (913290990387/607700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1013891219/5000000000 : ℝ)*X 0 0+(1085008531/2000000000 : ℝ)*X 0 1+(5232949653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352076353/10000000000 : ℝ)*X 1 0+(-1062957397/5000000000 : ℝ)*X 1 1+(209317983/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338019061/2500000000 : ℝ)*X 2 0+(1308237433/2500000000 : ℝ)*X 2 1+(-212591473/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540153517/1250000000 : ℝ)*X 0 0+(412316131/1000000000 : ℝ)*X 0 1+(2264044643/5000000000 : ℝ)*X 0 2+(540153517/1250000000 : ℝ)*X 1 0+(412316131/1000000000 : ℝ)*X 1 1+(2264044643/5000000000 : ℝ)*X 1 2+(540153517/1250000000 : ℝ)*X 2 0+(412316131/1000000000 : ℝ)*X 2 1+(2264044643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-405560147/2000000000 : ℝ)*X 0 0+(5233742411/10000000000 : ℝ)*X 0 1+(5424245217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302501233/10000000000 : ℝ)*X 1 0+(-483654801/2500000000 : ℝ)*X 1 1+(542424521/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325625271/2500000000 : ℝ)*X 2 0+(1084849063/2000000000 : ℝ)*X 2 1+(-15114213/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080316711/2500000000 : ℝ)*X 0 0+(565802249/1250000000 : ℝ)*X 0 1+(824968499/2000000000 : ℝ)*X 0 2+(1080316711/2500000000 : ℝ)*X 1 0+(565802249/1250000000 : ℝ)*X 1 1+(824968499/2000000000 : ℝ)*X 1 2+(1080316711/2500000000 : ℝ)*X 2 0+(565802249/1250000000 : ℝ)*X 2 1+(824968499/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1596450063689494185885144579/151925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1109200129/50000000000000 : ℝ)*(base19) + (2033364529/100000000000000 : ℝ)*(base23) + (5286039/12500000000000 : ℝ)*(lower2) + (14267843/6250000000000 : ℝ)*(upper3) + (109210791/50000000000000 : ℝ)*(upper5) + (383775508928067/10000000000000 : ℝ)*(major0) + (383775508928067/10000000000000 : ℝ)*(major1) + (383775508928067/10000000000000 : ℝ)*(major2) + (5205852774994099/100000000000000 : ℝ)*(sp0) + (5205891782386633/100000000000000 : ℝ)*(sp1) + (2602945983711181/50000000000000 : ℝ)*(sp2) + (123479763668829/5000000000000 : ℝ)*(sp3) + (5153224099/12500000000000 : ℝ)*(sp4) + (20554126329/100000000000000 : ℝ)*(sp7) + (246961582750291/10000000000000 : ℝ)*(f.failure) + (5205894000786891/100000000000000 : ℝ)*(f.sum) + (1051825912479/151925000000000000000000000 : ℝ)*base65 + (1189540289565292269/303850000000000000000000000000000 : ℝ)*base68 + (5308901805641142269/303850000000000000000000000000000 : ℝ)*base70 + (1307724108313292269/303850000000000000000000000000000 : ℝ)*base72 + (5373125307569/1519250000000000000000000000 : ℝ)*base73 + (4447443746077542269/303850000000000000000000000000000 : ℝ)*base76 + (2885306890697442269/303850000000000000000000000000000 : ℝ)*base78 + (2685063441279242269/303850000000000000000000000000000 : ℝ)*base80 + (12549600737283/6077000000000000000000000000 : ℝ)*base81 + (1357117/100000000000000000000 : ℝ)*base89 + (1357117/100000000000000000000 : ℝ)*base91 + (1357117/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5432669243022420430580439087/759625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (674328041/50000000000000 : ℝ)*(base19) + (1293153709/100000000000000 : ℝ)*(base23) + (135441989/100000000000000 : ℝ)*(upper3) + (3362951/6250000000000 : ℝ)*(lower4) + (1002059/625000000000 : ℝ)*(upper5) + (3869728033184253/100000000000000 : ℝ)*(major0) + (3869728033184253/100000000000000 : ℝ)*(major1) + (3869728033184253/100000000000000 : ℝ)*(major2) + (1561704079/6250000000000 : ℝ)*(sp1) + (4794794203/20000000000000 : ℝ)*(sp2) + (1049853048177177/20000000000000 : ℝ)*(sp4) + (2624619452482269/50000000000000 : ℝ)*(sp5) + (5249239973761161/100000000000000 : ℝ)*(sp6) + (1245095293545009/50000000000000 : ℝ)*(sp7) + (1245095293545009/50000000000000 : ℝ)*(f.failure) + (1049853048177177/20000000000000 : ℝ)*(f.sum) + (21104512872433/15192500000000000000000000000 : ℝ)*base65 + (39042641238081411971/3038500000000000000000000000000000 : ℝ)*base68 + (24457854498095411971/3038500000000000000000000000000000 : ℝ)*base70 + (17444993647259088029/3038500000000000000000000000000000 : ℝ)*base71 + (210972855551969/30385000000000000000000000000 : ℝ)*base74 + (23161520206892911971/3038500000000000000000000000000000 : ℝ)*base76 + (23048149779303911971/3038500000000000000000000000000000 : ℝ)*base78 + (41678418326541411971/3038500000000000000000000000000000 : ℝ)*base80 + (9486789090351/30385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4273983/500000000000000000000 : ℝ)*base89 + (4273983/500000000000000000000 : ℝ)*base91 + (4273983/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1359_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7497/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1359_s4_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63409761/312500000 : ℝ)*x 0 + (5414099543/10000000000 : ℝ)*x 1 + (5243018941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63409761/312500000 : ℝ)^4319 ≤ (12360467818129/100000000000000 : ℝ)^3295 := by
    have hnat : (63409761 : ℕ)^4319*100000000000000^3295 ≤ 12360467818129^3295*312500000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63409761 312500000 12360467818129 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414099543/10000000000 : ℝ)^4319 ≤ (8948353685399/20000000000000 : ℝ)^3295 := by
    have hnat : (5414099543 : ℕ)^4319*20000000000000^3295 ≤ 8948353685399^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414099543 10000000000 8948353685399 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243018941/10000000000 : ℝ)^4319 ≤ (5362220467727/12500000000000 : ℝ)^3295 := by
    have hnat : (5243018941 : ℕ)^4319*12500000000000^3295 ≤ 5362220467727^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243018941 10000000000 5362220467727 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63409761/312500000 : ℝ), (5414099543/10000000000 : ℝ), (5243018941/10000000000 : ℝ)] ![(12360467818129/100000000000000 : ℝ), (8948353685399/20000000000000 : ℝ), (5362220467727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63409761/312500000 : ℝ)|^4319 ≤ (12360467818129/100000000000000 : ℝ)^3295
        have hw : |(-63409761/312500000 : ℝ)|=(63409761/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414099543/10000000000 : ℝ)|^4319 ≤ (8948353685399/20000000000000 : ℝ)^3295
        have hw : |(5414099543/10000000000 : ℝ)|=(5414099543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243018941/10000000000 : ℝ)|^4319 ≤ (5362220467727/12500000000000 : ℝ)^3295
        have hw : |(5243018941/10000000000 : ℝ)|=(5243018941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s4_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674639921/5000000000 : ℝ)*x 0 + (-2116307931/10000000000 : ℝ)*x 1 + (1048603709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674639921/5000000000 : ℝ)^4319 ≤ (44040941489133/100000000000000 : ℝ)^3295 := by
    have hnat : (2674639921 : ℕ)^4319*100000000000000^3295 ≤ 44040941489133^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674639921 5000000000 44040941489133 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116307931/10000000000 : ℝ)^4319 ≤ (3265324750383/25000000000000 : ℝ)^3295 := by
    have hnat : (2116307931 : ℕ)^4319*25000000000000^3295 ≤ 3265324750383^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116307931 10000000000 3265324750383 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048603709/2000000000 : ℝ)^4319 ≤ (10724439873719/25000000000000 : ℝ)^3295 := by
    have hnat : (1048603709 : ℕ)^4319*25000000000000^3295 ≤ 10724439873719^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048603709 2000000000 10724439873719 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674639921/5000000000 : ℝ), (-2116307931/10000000000 : ℝ), (1048603709/2000000000 : ℝ)] ![(44040941489133/100000000000000 : ℝ), (3265324750383/25000000000000 : ℝ), (10724439873719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674639921/5000000000 : ℝ)|^4319 ≤ (44040941489133/100000000000000 : ℝ)^3295
        have hw : |(2674639921/5000000000 : ℝ)|=(2674639921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116307931/10000000000 : ℝ)|^4319 ≤ (3265324750383/25000000000000 : ℝ)^3295
        have hw : |(-2116307931/10000000000 : ℝ)|=(2116307931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048603709/2000000000 : ℝ)|^4319 ≤ (10724439873719/25000000000000 : ℝ)^3295
        have hw : |(1048603709/2000000000 : ℝ)|=(1048603709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s4_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337319879/2500000000 : ℝ)*x 0 + (1310754731/2500000000 : ℝ)*x 1 + (-264538483/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337319879/2500000000 : ℝ)^4319 ≤ (8808187594209/20000000000000 : ℝ)^3295 := by
    have hnat : (1337319879 : ℕ)^4319*20000000000000^3295 ≤ 8808187594209^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337319879 2500000000 8808187594209 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310754731/2500000000 : ℝ)^4319 ≤ (21448881779749/50000000000000 : ℝ)^3295 := by
    have hnat : (1310754731 : ℕ)^4319*50000000000000^3295 ≤ 21448881779749^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310754731 2500000000 21448881779749 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264538483/1250000000 : ℝ)^4319 ≤ (13061298459519/100000000000000 : ℝ)^3295 := by
    have hnat : (264538483 : ℕ)^4319*100000000000000^3295 ≤ 13061298459519^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264538483 1250000000 13061298459519 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337319879/2500000000 : ℝ), (1310754731/2500000000 : ℝ), (-264538483/1250000000 : ℝ)] ![(8808187594209/20000000000000 : ℝ), (21448881779749/50000000000000 : ℝ), (13061298459519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337319879/2500000000 : ℝ)|^4319 ≤ (8808187594209/20000000000000 : ℝ)^3295
        have hw : |(1337319879/2500000000 : ℝ)|=(1337319879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310754731/2500000000 : ℝ)|^4319 ≤ (21448881779749/50000000000000 : ℝ)^3295
        have hw : |(1310754731/2500000000 : ℝ)|=(1310754731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264538483/1250000000 : ℝ)|^4319 ≤ (13061298459519/100000000000000 : ℝ)^3295
        have hw : |(-264538483/1250000000 : ℝ)|=(264538483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s4_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135063649/312500000 : ℝ)*x 0 + (4145208769/10000000000 : ℝ)*x 1 + (1126460671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135063649/312500000 : ℝ)^4319 ≤ (8325492748743/25000000000000 : ℝ)^3295 := by
    have hnat : (135063649 : ℕ)^4319*25000000000000^3295 ≤ 8325492748743^3295*312500000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135063649 312500000 8325492748743 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145208769/10000000000 : ℝ)^4319 ≤ (31527520299039/100000000000000 : ℝ)^3295 := by
    have hnat : (4145208769 : ℕ)^4319*100000000000000^3295 ≤ 31527520299039^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145208769 10000000000 31527520299039 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126460671/2500000000 : ℝ)^4319 ≤ (17585254344857/50000000000000 : ℝ)^3295 := by
    have hnat : (1126460671 : ℕ)^4319*50000000000000^3295 ≤ 17585254344857^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126460671 2500000000 17585254344857 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135063649/312500000 : ℝ), (4145208769/10000000000 : ℝ), (1126460671/2500000000 : ℝ)] ![(8325492748743/25000000000000 : ℝ), (31527520299039/100000000000000 : ℝ), (17585254344857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135063649/312500000 : ℝ)|^4319 ≤ (8325492748743/25000000000000 : ℝ)^3295
        have hw : |(135063649/312500000 : ℝ)|=(135063649/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145208769/10000000000 : ℝ)|^4319 ≤ (31527520299039/100000000000000 : ℝ)^3295
        have hw : |(4145208769/10000000000 : ℝ)|=(4145208769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126460671/2500000000 : ℝ)|^4319 ≤ (17585254344857/50000000000000 : ℝ)^3295
        have hw : |(1126460671/2500000000 : ℝ)|=(1126460671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s4_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029125673/10000000000 : ℝ)*x 0 + (65545599/125000000 : ℝ)*x 1 + (5413466967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029125673/10000000000 : ℝ)^4319 ≤ (2472114836387/20000000000000 : ℝ)^3295 := by
    have hnat : (2029125673 : ℕ)^4319*20000000000000^3295 ≤ 2472114836387^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029125673 10000000000 2472114836387 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65545599/125000000 : ℝ)^4319 ≤ (42904509414317/100000000000000 : ℝ)^3295 := by
    have hnat : (65545599 : ℕ)^4319*100000000000000^3295 ≤ 42904509414317^3295*125000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65545599 125000000 42904509414317 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413466967/10000000000 : ℝ)^4319 ≤ (5591864549103/12500000000000 : ℝ)^3295 := by
    have hnat : (5413466967 : ℕ)^4319*12500000000000^3295 ≤ 5591864549103^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413466967 10000000000 5591864549103 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029125673/10000000000 : ℝ), (65545599/125000000 : ℝ), (5413466967/10000000000 : ℝ)] ![(2472114836387/20000000000000 : ℝ), (42904509414317/100000000000000 : ℝ), (5591864549103/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029125673/10000000000 : ℝ)|^4319 ≤ (2472114836387/20000000000000 : ℝ)^3295
        have hw : |(-2029125673/10000000000 : ℝ)|=(2029125673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65545599/125000000 : ℝ)|^4319 ≤ (42904509414317/100000000000000 : ℝ)^3295
        have hw : |(65545599/125000000 : ℝ)|=(65545599/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413466967/10000000000 : ℝ)|^4319 ≤ (5591864549103/12500000000000 : ℝ)^3295
        have hw : |(5413466967/10000000000 : ℝ)|=(5413466967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s4_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663140957/1250000000 : ℝ)*x 0 + (-389171979/2000000000 : ℝ)*x 1 + (1353366799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663140957/1250000000 : ℝ)^4319 ≤ (21782538743571/50000000000000 : ℝ)^3295 := by
    have hnat : (663140957 : ℕ)^4319*50000000000000^3295 ≤ 21782538743571^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663140957 1250000000 21782538743571 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389171979/2000000000 : ℝ)^4319 ≤ (11700003631311/100000000000000 : ℝ)^3295 := by
    have hnat : (389171979 : ℕ)^4319*100000000000000^3295 ≤ 11700003631311^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389171979 2000000000 11700003631311 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353366799/2500000000 : ℝ)^4319 ≤ (44734918873297/100000000000000 : ℝ)^3295 := by
    have hnat : (1353366799 : ℕ)^4319*100000000000000^3295 ≤ 44734918873297^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353366799 2500000000 44734918873297 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663140957/1250000000 : ℝ), (-389171979/2000000000 : ℝ), (1353366799/2500000000 : ℝ)] ![(21782538743571/50000000000000 : ℝ), (11700003631311/100000000000000 : ℝ), (44734918873297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663140957/1250000000 : ℝ)|^4319 ≤ (21782538743571/50000000000000 : ℝ)^3295
        have hw : |(663140957/1250000000 : ℝ)|=(663140957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389171979/2000000000 : ℝ)|^4319 ≤ (11700003631311/100000000000000 : ℝ)^3295
        have hw : |(-389171979/2000000000 : ℝ)|=(389171979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353366799/2500000000 : ℝ)|^4319 ≤ (44734918873297/100000000000000 : ℝ)^3295
        have hw : |(1353366799/2500000000 : ℝ)|=(1353366799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s4_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061025577/2000000000 : ℝ)*x 0 + (1353366683/2500000000 : ℝ)*x 1 + (-1945860219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061025577/2000000000 : ℝ)^4319 ≤ (544563499401/1250000000000 : ℝ)^3295 := by
    have hnat : (1061025577 : ℕ)^4319*1250000000000^3295 ≤ 544563499401^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061025577 2000000000 544563499401 1250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353366683/2500000000 : ℝ)^4319 ≤ (44734913847361/100000000000000 : ℝ)^3295 := by
    have hnat : (1353366683 : ℕ)^4319*100000000000000^3295 ≤ 44734913847361^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353366683 2500000000 44734913847361 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945860219/10000000000 : ℝ)^4319 ≤ (5850003092439/50000000000000 : ℝ)^3295 := by
    have hnat : (1945860219 : ℕ)^4319*50000000000000^3295 ≤ 5850003092439^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945860219 10000000000 5850003092439 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061025577/2000000000 : ℝ), (1353366683/2500000000 : ℝ), (-1945860219/10000000000 : ℝ)] ![(544563499401/1250000000000 : ℝ), (44734913847361/100000000000000 : ℝ), (5850003092439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061025577/2000000000 : ℝ)|^4319 ≤ (544563499401/1250000000000 : ℝ)^3295
        have hw : |(1061025577/2000000000 : ℝ)|=(1061025577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353366683/2500000000 : ℝ)|^4319 ≤ (44734913847361/100000000000000 : ℝ)^3295
        have hw : |(1353366683/2500000000 : ℝ)|=(1353366683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945860219/10000000000 : ℝ)|^4319 ≤ (5850003092439/50000000000000 : ℝ)^3295
        have hw : |(-1945860219/10000000000 : ℝ)|=(1945860219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s4_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322064553/10000000000 : ℝ)*x 0 + (2252257981/5000000000 : ℝ)*x 1 + (207327103/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322064553/10000000000 : ℝ)^4319 ≤ (33302251615929/100000000000000 : ℝ)^3295 := by
    have hnat : (4322064553 : ℕ)^4319*100000000000000^3295 ≤ 33302251615929^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322064553 10000000000 33302251615929 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252257981/5000000000 : ℝ)^4319 ≤ (7031387046559/20000000000000 : ℝ)^3295 := by
    have hnat : (2252257981 : ℕ)^4319*20000000000000^3295 ≤ 7031387046559^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252257981 5000000000 7031387046559 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207327103/500000000 : ℝ)^4319 ≤ (15770406570511/50000000000000 : ℝ)^3295 := by
    have hnat : (207327103 : ℕ)^4319*50000000000000^3295 ≤ 15770406570511^3295*500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207327103 500000000 15770406570511 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322064553/10000000000 : ℝ), (2252257981/5000000000 : ℝ), (207327103/500000000 : ℝ)] ![(33302251615929/100000000000000 : ℝ), (7031387046559/20000000000000 : ℝ), (15770406570511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322064553/10000000000 : ℝ)|^4319 ≤ (33302251615929/100000000000000 : ℝ)^3295
        have hw : |(4322064553/10000000000 : ℝ)|=(4322064553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252257981/5000000000 : ℝ)|^4319 ≤ (7031387046559/20000000000000 : ℝ)^3295
        have hw : |(2252257981/5000000000 : ℝ)|=(2252257981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207327103/500000000 : ℝ)|^4319 ≤ (15770406570511/50000000000000 : ℝ)^3295
        have hw : |(207327103/500000000 : ℝ)|=(207327103/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7497/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7497/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7497/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7497/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7497/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7497/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7497/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (683/6250 : ℝ) ^ (2159/512 : ℝ) ≤ (1103141908277037/12500000000000000000 : ℝ) := by
    have hpowers : (683/6250 : ℝ)^2159 ≤ (1103141908277037/12500000000000000000 : ℝ)^512 := by
      have hnat : (683 : ℕ)^2159*12500000000000000000^512 ≤ 1103141908277037^512*6250^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        683 6250 1103141908277037 12500000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (683/6250 : ℝ)) (X := (1103141908277037/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7497/50000 : ℝ) ^ (2159/512 : ℝ) ≤ (16748716097868359/50000000000000000000 : ℝ) := by
    have hpowers : (7497/50000 : ℝ)^2159 ≤ (16748716097868359/50000000000000000000 : ℝ)^512 := by
      have hnat : (7497 : ℕ)^2159*50000000000000000000^512 ≤ 16748716097868359^512*50000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7497 50000 16748716097868359 50000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7497/50000 : ℝ)) (X := (16748716097868359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251103141908277037/6250000000000000000 : ℝ) ≤ (1000041854238923/1000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (6251103141908277037/6250000000000000000 : ℝ)^512 ≤ (1000041854238923/1000000000000000 : ℝ)^2159 := by
      have hnat : (6251103141908277037 : ℕ)^512*1000000000000000^2159 ≤ 1000041854238923^2159*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251103141908277037 6250000000000000000 1000041854238923 1000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000041854238923/1000000000000000 : ℝ)) (X := (6251103141908277037/6250000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021161283730976507/50000000000000000000 : ℝ) ≤ (10001003504278319/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (50021161283730976507/50000000000000000000 : ℝ)^512 ≤ (10001003504278319/10000000000000000 : ℝ)^2159 := by
      have hnat : (50021161283730976507 : ℕ)^512*10000000000000000^2159 ≤ 10001003504278319^2159*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021161283730976507 50000000000000000000 10001003504278319 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001003504278319/10000000000000000 : ℝ)) (X := (50021161283730976507/50000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016748716097868359/25000000000000000000 : ℝ) ≤ (625099279135463/625000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (25016748716097868359/25000000000000000000 : ℝ)^512 ≤ (625099279135463/625000000000000 : ℝ)^2159 := by
      have hnat : (25016748716097868359 : ℕ)^512*625000000000000^2159 ≤ 625099279135463^2159*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016748716097868359 25000000000000000000 625099279135463 625000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625099279135463/625000000000000 : ℝ)) (X := (25016748716097868359/25000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1103141908277037/12500000000000000000 : ℝ) ≤ ((10162229216576669999/10165000000000000000 : ℝ)+2*(584961889089/406600000000000 : ℝ)*(683/6250 : ℝ))^(2159/512 : ℝ) := by
    rw [show (10162229216576669999/10165000000000000000 : ℝ)+2*(584961889089/406600000000000 : ℝ)*(683/6250 : ℝ)=(1000041854238923/1000000000000000 : ℝ) by norm_num, show 1+2*(1103141908277037/12500000000000000000 : ℝ)=(6251103141908277037/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16748716097868359/50000000000000000000 : ℝ)+(1103141908277037/12500000000000000000 : ℝ) ≤ ((10162229216576669999/10165000000000000000 : ℝ)+(584961889089/406600000000000 : ℝ)*((7497/50000 : ℝ)+(683/6250 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (10162229216576669999/10165000000000000000 : ℝ)+(584961889089/406600000000000 : ℝ)*((7497/50000 : ℝ)+(683/6250 : ℝ))=(10001003504278319/10000000000000000 : ℝ) by norm_num, show 1+(16748716097868359/50000000000000000000 : ℝ)+(1103141908277037/12500000000000000000 : ℝ)=(50021161283730976507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16748716097868359/50000000000000000000 : ℝ) ≤ ((10162229216576669999/10165000000000000000 : ℝ)+2*(584961889089/406600000000000 : ℝ)*(7497/50000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (10162229216576669999/10165000000000000000 : ℝ)+2*(584961889089/406600000000000 : ℝ)*(7497/50000 : ℝ)=(625099279135463/625000000000000 : ℝ) by norm_num, show 1+2*(16748716097868359/50000000000000000000 : ℝ)=(25016748716097868359/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10162229216576669999/10165000000000000000 : ℝ)*(X 1 0+X 2 0)+(584961889089/406600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (7497/50000 : ℝ)) (c := (10162229216576669999/10165000000000000000 : ℝ)) (alpha := (584961889089/406600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10162229216576669999/10165000000000000000 : ℝ)*(X 0 1+X 2 1)+(584961889089/406600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (7497/50000 : ℝ)) (c := (10162229216576669999/10165000000000000000 : ℝ)) (alpha := (584961889089/406600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10162229216576669999/10165000000000000000 : ℝ)*(X 0 2+X 1 2)+(584961889089/406600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (7497/50000 : ℝ)) (c := (10162229216576669999/10165000000000000000 : ℝ)) (alpha := (584961889089/406600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-63409761/312500000 : ℝ)*X 0 0+(5414099543/10000000000 : ℝ)*X 0 1+(5243018941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674639921/5000000000 : ℝ)*X 1 0+(-2116307931/10000000000 : ℝ)*X 1 1+(1048603709/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337319879/2500000000 : ℝ)*X 2 0+(1310754731/2500000000 : ℝ)*X 2 1+(-264538483/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135063649/312500000 : ℝ)*X 0 0+(4145208769/10000000000 : ℝ)*X 0 1+(1126460671/2500000000 : ℝ)*X 0 2+(135063649/312500000 : ℝ)*X 1 0+(4145208769/10000000000 : ℝ)*X 1 1+(1126460671/2500000000 : ℝ)*X 1 2+(135063649/312500000 : ℝ)*X 2 0+(4145208769/10000000000 : ℝ)*X 2 1+(1126460671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2029125673/10000000000 : ℝ)*X 0 0+(65545599/125000000 : ℝ)*X 0 1+(5413466967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663140957/1250000000 : ℝ)*X 1 0+(-389171979/2000000000 : ℝ)*X 1 1+(1353366799/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061025577/2000000000 : ℝ)*X 2 0+(1353366683/2500000000 : ℝ)*X 2 1+(-1945860219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322064553/10000000000 : ℝ)*X 0 0+(2252257981/5000000000 : ℝ)*X 0 1+(207327103/500000000 : ℝ)*X 0 2+(4322064553/10000000000 : ℝ)*X 1 0+(2252257981/5000000000 : ℝ)*X 1 1+(207327103/500000000 : ℝ)*X 1 2+(4322064553/10000000000 : ℝ)*X 2 0+(2252257981/5000000000 : ℝ)*X 2 1+(207327103/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1223074927414339620996167373/101650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43730243/2000000000000 : ℝ)*(base19) + (29920073/2000000000000 : ℝ)*(base23) + (178816527/100000000000000 : ℝ)*(lower2) + (121810739/50000000000000 : ℝ)*(upper3) + (2994259/20000000000000 : ℝ)*(upper5) + (861820058858597/20000000000000 : ℝ)*(major0) + (861820058858597/20000000000000 : ℝ)*(major1) + (861820058858597/20000000000000 : ℝ)*(major2) + (292261903114003/5000000000000 : ℝ)*(sp0) + (2922634512600841/50000000000000 : ℝ)*(sp1) + (2922634857855091/50000000000000 : ℝ)*(sp2) + (173306891245961/6250000000000 : ℝ)*(sp3) + (33149433773/100000000000000 : ℝ)*(sp4) + (1871586283/10000000000000 : ℝ)*(sp7) + (1386464487899103/50000000000000 : ℝ)*(f.failure) + (5845271211713833/100000000000000 : ℝ)*(f.sum) + (25165502238861/4066000000000000000000000000 : ℝ)*base66 + (2518852110141256403/203300000000000000000000000000000 : ℝ)*base67 + (3496787606390956403/203300000000000000000000000000000 : ℝ)*base69 + (895573851169856403/203300000000000000000000000000000 : ℝ)*base71 + (6051008432441/4066000000000000000000000000 : ℝ)*base73 + (655690489452256403/203300000000000000000000000000000 : ℝ)*base75 + (395834463265456403/203300000000000000000000000000000 : ℝ)*base77 + (1914589735428856403/203300000000000000000000000000000 : ℝ)*base79 + (949354946443/4066000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3021361/500000000000000000000 : ℝ)*base89 + (3021361/500000000000000000000 : ℝ)*base91 + (3021361/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1178231587964853867824816607/254125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (283163303/100000000000000 : ℝ)*(base19) + (518795403/100000000000000 : ℝ)*(base23) + (76194717/100000000000000 : ℝ)*(upper3) + (47000317/100000000000000 : ℝ)*(lower4) + (221659951/100000000000000 : ℝ)*(upper5) + (2170531969768869/50000000000000 : ℝ)*(major0) + (2170531969768869/50000000000000 : ℝ)*(major1) + (2170531969768869/50000000000000 : ℝ)*(major2) + (1813856479/100000000000000 : ℝ)*(sp0) + (321864547/2500000000000 : ℝ)*(sp1) + (2944314079511309/50000000000000 : ℝ)*(sp4) + (2944308407566957/50000000000000 : ℝ)*(sp5) + (2944314727041847/50000000000000 : ℝ)*(sp6) + (1396748875824431/50000000000000 : ℝ)*(sp7) + (1396748875824431/50000000000000 : ℝ)*(f.failure) + (5888629972879097/100000000000000 : ℝ)*(f.sum) + (56971642283281/10165000000000000000000000000 : ℝ)*base65 + (1126589458541736131/508250000000000000000000000000000 : ℝ)*base67 + (5413533273938736131/508250000000000000000000000000000 : ℝ)*base69 + (6736704632827486131/508250000000000000000000000000000 : ℝ)*base71 + (49338969751231/10165000000000000000000000000 : ℝ)*base73 + (1979278802103013869/508250000000000000000000000000000 : ℝ)*base76 + (1249729805997986131/508250000000000000000000000000000 : ℝ)*base77 + (1354953542854013869/508250000000000000000000000000000 : ℝ)*base80 + (90561086119231/10165000000000000000000000000 : ℝ)*base81 + (420703/500000000000000000000 : ℝ)*base90 + (420703/500000000000000000000 : ℝ)*base92 + (420703/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1359_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7497/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1359_s5_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029336699/10000000000 : ℝ)*x 0 + (5412163411/10000000000 : ℝ)*x 1 + (5244807253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029336699/10000000000 : ℝ)^4319 ≤ (98898073473/800000000000 : ℝ)^3295 := by
    have hnat : (2029336699 : ℕ)^4319*800000000000^3295 ≤ 98898073473^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029336699 10000000000 98898073473 800000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412163411/10000000000 : ℝ)^4319 ≤ (44720797118839/100000000000000 : ℝ)^3295 := by
    have hnat : (5412163411 : ℕ)^4319*100000000000000^3295 ≤ 44720797118839^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412163411 10000000000 44720797118839 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244807253/10000000000 : ℝ)^4319 ≤ (42916943685051/100000000000000 : ℝ)^3295 := by
    have hnat : (5244807253 : ℕ)^4319*100000000000000^3295 ≤ 42916943685051^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244807253 10000000000 42916943685051 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029336699/10000000000 : ℝ), (5412163411/10000000000 : ℝ), (5244807253/10000000000 : ℝ)] ![(98898073473/800000000000 : ℝ), (44720797118839/100000000000000 : ℝ), (42916943685051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029336699/10000000000 : ℝ)|^4319 ≤ (98898073473/800000000000 : ℝ)^3295
        have hw : |(-2029336699/10000000000 : ℝ)|=(2029336699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412163411/10000000000 : ℝ)|^4319 ≤ (44720797118839/100000000000000 : ℝ)^3295
        have hw : |(5412163411/10000000000 : ℝ)|=(5412163411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244807253/10000000000 : ℝ)|^4319 ≤ (42916943685051/100000000000000 : ℝ)^3295
        have hw : |(5244807253/10000000000 : ℝ)|=(5244807253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s5_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674391703/5000000000 : ℝ)*x 0 + (-2114598489/10000000000 : ℝ)*x 1 + (1048961457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674391703/5000000000 : ℝ)^4319 ≤ (22017792093953/50000000000000 : ℝ)^3295 := by
    have hnat : (2674391703 : ℕ)^4319*50000000000000^3295 ≤ 22017792093953^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674391703 5000000000 22017792093953 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114598489/10000000000 : ℝ)^4319 ≤ (13047471772899/100000000000000 : ℝ)^3295 := by
    have hnat : (2114598489 : ℕ)^4319*100000000000000^3295 ≤ 13047471772899^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114598489 10000000000 13047471772899 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048961457/2000000000 : ℝ)^4319 ≤ (1716677761131/4000000000000 : ℝ)^3295 := by
    have hnat : (1048961457 : ℕ)^4319*4000000000000^3295 ≤ 1716677761131^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048961457 2000000000 1716677761131 4000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674391703/5000000000 : ℝ), (-2114598489/10000000000 : ℝ), (1048961457/2000000000 : ℝ)] ![(22017792093953/50000000000000 : ℝ), (13047471772899/100000000000000 : ℝ), (1716677761131/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674391703/5000000000 : ℝ)|^4319 ≤ (22017792093953/50000000000000 : ℝ)^3295
        have hw : |(2674391703/5000000000 : ℝ)|=(2674391703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114598489/10000000000 : ℝ)|^4319 ≤ (13047471772899/100000000000000 : ℝ)^3295
        have hw : |(-2114598489/10000000000 : ℝ)|=(2114598489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048961457/2000000000 : ℝ)|^4319 ≤ (1716677761131/4000000000000 : ℝ)^3295
        have hw : |(1048961457/2000000000 : ℝ)|=(1048961457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s5_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348783407/10000000000 : ℝ)*x 0 + (5244807297/10000000000 : ℝ)*x 1 + (-2114598471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348783407/10000000000 : ℝ)^4319 ≤ (22017792099349/50000000000000 : ℝ)^3295 := by
    have hnat : (5348783407 : ℕ)^4319*50000000000000^3295 ≤ 22017792099349^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348783407 10000000000 22017792099349 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244807297/10000000000 : ℝ)^4319 ≤ (42916944156983/100000000000000 : ℝ)^3295 := by
    have hnat : (5244807297 : ℕ)^4319*100000000000000^3295 ≤ 42916944156983^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244807297 10000000000 42916944156983 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114598471/10000000000 : ℝ)^4319 ≤ (326186790683/2500000000000 : ℝ)^3295 := by
    have hnat : (2114598471 : ℕ)^4319*2500000000000^3295 ≤ 326186790683^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114598471 10000000000 326186790683 2500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348783407/10000000000 : ℝ), (5244807297/10000000000 : ℝ), (-2114598471/10000000000 : ℝ)] ![(22017792099349/50000000000000 : ℝ), (42916944156983/100000000000000 : ℝ), (326186790683/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348783407/10000000000 : ℝ)|^4319 ≤ (22017792099349/50000000000000 : ℝ)^3295
        have hw : |(5348783407/10000000000 : ℝ)|=(5348783407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244807297/10000000000 : ℝ)|^4319 ≤ (42916944156983/100000000000000 : ℝ)^3295
        have hw : |(5244807297/10000000000 : ℝ)|=(5244807297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2114598471/10000000000 : ℝ)|^4319 ≤ (326186790683/2500000000000 : ℝ)^3295
        have hw : |(-2114598471/10000000000 : ℝ)|=(2114598471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s5_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540271329/1250000000 : ℝ)*x 0 + (259319853/625000000 : ℝ)*x 1 + (900380121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540271329/1250000000 : ℝ)^4319 ≤ (16651661495093/50000000000000 : ℝ)^3295 := by
    have hnat : (540271329 : ℕ)^4319*50000000000000^3295 ≤ 16651661495093^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540271329 1250000000 16651661495093 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259319853/625000000 : ℝ)^4319 ≤ (3156649538087/10000000000000 : ℝ)^3295 := by
    have hnat : (259319853 : ℕ)^4319*10000000000000^3295 ≤ 3156649538087^3295*625000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259319853 625000000 3156649538087 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900380121/2000000000 : ℝ)^4319 ≤ (17565090809473/50000000000000 : ℝ)^3295 := by
    have hnat : (900380121 : ℕ)^4319*50000000000000^3295 ≤ 17565090809473^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900380121 2000000000 17565090809473 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540271329/1250000000 : ℝ), (259319853/625000000 : ℝ), (900380121/2000000000 : ℝ)] ![(16651661495093/50000000000000 : ℝ), (3156649538087/10000000000000 : ℝ), (17565090809473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540271329/1250000000 : ℝ)|^4319 ≤ (16651661495093/50000000000000 : ℝ)^3295
        have hw : |(540271329/1250000000 : ℝ)|=(540271329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259319853/625000000 : ℝ)|^4319 ≤ (3156649538087/10000000000000 : ℝ)^3295
        have hw : |(259319853/625000000 : ℝ)|=(259319853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900380121/2000000000 : ℝ)|^4319 ≤ (17565090809473/50000000000000 : ℝ)^3295
        have hw : |(900380121/2000000000 : ℝ)|=(900380121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s5_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1014674299/5000000000 : ℝ)*x 0 + (1311352469/2500000000 : ℝ)*x 1 + (676444731/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014674299/5000000000 : ℝ)^4319 ≤ (12362354196983/100000000000000 : ℝ)^3295 := by
    have hnat : (1014674299 : ℕ)^4319*100000000000000^3295 ≤ 12362354196983^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014674299 5000000000 12362354196983 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311352469/2500000000 : ℝ)^4319 ≤ (42923407374697/100000000000000 : ℝ)^3295 := by
    have hnat : (1311352469 : ℕ)^4319*100000000000000^3295 ≤ 42923407374697^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311352469 2500000000 42923407374697 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676444731/1250000000 : ℝ)^4319 ≤ (1788569536491/4000000000000 : ℝ)^3295 := by
    have hnat : (676444731 : ℕ)^4319*4000000000000^3295 ≤ 1788569536491^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676444731 1250000000 1788569536491 4000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1014674299/5000000000 : ℝ), (1311352469/2500000000 : ℝ), (676444731/1250000000 : ℝ)] ![(12362354196983/100000000000000 : ℝ), (42923407374697/100000000000000 : ℝ), (1788569536491/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1014674299/5000000000 : ℝ)|^4319 ≤ (12362354196983/100000000000000 : ℝ)^3295
        have hw : |(-1014674299/5000000000 : ℝ)|=(1014674299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311352469/2500000000 : ℝ)|^4319 ≤ (42923407374697/100000000000000 : ℝ)^3295
        have hw : |(1311352469/2500000000 : ℝ)|=(1311352469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676444731/1250000000 : ℝ)|^4319 ≤ (1788569536491/4000000000000 : ℝ)^3295
        have hw : |(676444731/1250000000 : ℝ)|=(676444731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s5_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305592569/10000000000 : ℝ)*x 0 + (-97392399/500000000 : ℝ)*x 1 + (338222393/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305592569/10000000000 : ℝ)^4319 ≤ (10892520460337/25000000000000 : ℝ)^3295 := by
    have hnat : (5305592569 : ℕ)^4319*25000000000000^3295 ≤ 10892520460337^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305592569 10000000000 10892520460337 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97392399/500000000 : ℝ)^4319 ≤ (5857837484871/50000000000000 : ℝ)^3295 := by
    have hnat : (97392399 : ℕ)^4319*50000000000000^3295 ≤ 5857837484871^3295*500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97392399 500000000 5857837484871 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338222393/625000000 : ℝ)^4319 ≤ (22357121588863/50000000000000 : ℝ)^3295 := by
    have hnat : (338222393 : ℕ)^4319*50000000000000^3295 ≤ 22357121588863^3295*625000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338222393 625000000 22357121588863 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305592569/10000000000 : ℝ), (-97392399/500000000 : ℝ), (338222393/625000000 : ℝ)] ![(10892520460337/25000000000000 : ℝ), (5857837484871/50000000000000 : ℝ), (22357121588863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305592569/10000000000 : ℝ)|^4319 ≤ (10892520460337/25000000000000 : ℝ)^3295
        have hw : |(5305592569/10000000000 : ℝ)|=(5305592569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97392399/500000000 : ℝ)|^4319 ≤ (5857837484871/50000000000000 : ℝ)^3295
        have hw : |(-97392399/500000000 : ℝ)|=(97392399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338222393/625000000 : ℝ)|^4319 ≤ (22357121588863/50000000000000 : ℝ)^3295
        have hw : |(338222393/625000000 : ℝ)|=(338222393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s5_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072497/3906250 : ℝ)*x 0 + (2705779313/5000000000 : ℝ)*x 1 + (-389569571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072497/3906250 : ℝ)^4319 ≤ (43570079161059/100000000000000 : ℝ)^3295 := by
    have hnat : (2072497 : ℕ)^4319*100000000000000^3295 ≤ 43570079161059^3295*3906250^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072497 3906250 43570079161059 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705779313/5000000000 : ℝ)^4319 ≤ (44714246838459/100000000000000 : ℝ)^3295 := by
    have hnat : (2705779313 : ℕ)^4319*100000000000000^3295 ≤ 44714246838459^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705779313 5000000000 44714246838459 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389569571/2000000000 : ℝ)^4319 ≤ (11715673984257/100000000000000 : ℝ)^3295 := by
    have hnat : (389569571 : ℕ)^4319*100000000000000^3295 ≤ 11715673984257^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389569571 2000000000 11715673984257 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072497/3906250 : ℝ), (2705779313/5000000000 : ℝ), (-389569571/2000000000 : ℝ)] ![(43570079161059/100000000000000 : ℝ), (44714246838459/100000000000000 : ℝ), (11715673984257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072497/3906250 : ℝ)|^4319 ≤ (43570079161059/100000000000000 : ℝ)^3295
        have hw : |(2072497/3906250 : ℝ)|=(2072497/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705779313/5000000000 : ℝ)|^4319 ≤ (44714246838459/100000000000000 : ℝ)^3295
        have hw : |(2705779313/5000000000 : ℝ)|=(2705779313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389569571/2000000000 : ℝ)|^4319 ≤ (11715673984257/100000000000000 : ℝ)^3295
        have hw : |(-389569571/2000000000 : ℝ)|=(389569571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s5_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322195991/10000000000 : ℝ)*x 0 + (4500631227/10000000000 : ℝ)*x 1 + (1037598457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322195991/10000000000 : ℝ)^4319 ≤ (6660715822329/20000000000000 : ℝ)^3295 := by
    have hnat : (4322195991 : ℕ)^4319*20000000000000^3295 ≤ 6660715822329^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322195991 10000000000 6660715822329 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500631227/10000000000 : ℝ)^4319 ≤ (877929958629/2500000000000 : ℝ)^3295 := by
    have hnat : (4500631227 : ℕ)^4319*2500000000000^3295 ≤ 877929958629^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500631227 10000000000 877929958629 2500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037598457/2500000000 : ℝ)^4319 ≤ (6315844505761/20000000000000 : ℝ)^3295 := by
    have hnat : (1037598457 : ℕ)^4319*20000000000000^3295 ≤ 6315844505761^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037598457 2500000000 6315844505761 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322195991/10000000000 : ℝ), (4500631227/10000000000 : ℝ), (1037598457/2500000000 : ℝ)] ![(6660715822329/20000000000000 : ℝ), (877929958629/2500000000000 : ℝ), (6315844505761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322195991/10000000000 : ℝ)|^4319 ≤ (6660715822329/20000000000000 : ℝ)^3295
        have hw : |(4322195991/10000000000 : ℝ)|=(4322195991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500631227/10000000000 : ℝ)|^4319 ≤ (877929958629/2500000000000 : ℝ)^3295
        have hw : |(4500631227/10000000000 : ℝ)|=(4500631227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037598457/2500000000 : ℝ)|^4319 ≤ (6315844505761/20000000000000 : ℝ)^3295
        have hw : |(1037598457/2500000000 : ℝ)|=(1037598457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5591/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (589/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11143/100000 : ℝ) ^ (2159/512 : ℝ) ≤ (4790397658949187/50000000000000000000 : ℝ) := by
    have hpowers : (11143/100000 : ℝ)^2159 ≤ (4790397658949187/50000000000000000000 : ℝ)^512 := by
      have hnat : (11143 : ℕ)^2159*50000000000000000000^512 ≤ 4790397658949187^512*100000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11143 100000 4790397658949187 50000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11143/100000 : ℝ)) (X := (4790397658949187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (2159/512 : ℝ) ≤ (31392522456272557/100000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^2159 ≤ (31392522456272557/100000000000000000000 : ℝ)^512 := by
      have hnat : (2953 : ℕ)^2159*100000000000000000000^512 ≤ 31392522456272557^512*20000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 31392522456272557 100000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (31392522456272557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004790397658949187/25000000000000000000 : ℝ) ≤ (10000454377834423/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (25004790397658949187/25000000000000000000 : ℝ)^512 ≤ (10000454377834423/10000000000000000 : ℝ)^2159 := by
      have hnat : (25004790397658949187 : ℕ)^512*10000000000000000^2159 ≤ 10000454377834423^2159*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004790397658949187 25000000000000000000 10000454377834423 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000454377834423/10000000000000000 : ℝ)) (X := (25004790397658949187/25000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040973317774170931/100000000000000000000 : ℝ) ≤ (10000971517412189/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (100040973317774170931/100000000000000000000 : ℝ)^512 ≤ (10000971517412189/10000000000000000 : ℝ)^2159 := by
      have hnat : (100040973317774170931 : ℕ)^512*10000000000000000^2159 ≤ 10000971517412189^2159*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040973317774170931 100000000000000000000 10000971517412189 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000971517412189/10000000000000000 : ℝ)) (X := (100040973317774170931/100000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031392522456272557/50000000000000000000 : ℝ) ≤ (2000297731397991/2000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (50031392522456272557/50000000000000000000 : ℝ)^512 ≤ (2000297731397991/2000000000000000 : ℝ)^2159 := by
      have hnat : (50031392522456272557 : ℕ)^512*2000000000000000^2159 ≤ 2000297731397991^2159*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031392522456272557 50000000000000000000 2000297731397991 2000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000297731397991/2000000000000000 : ℝ)) (X := (50031392522456272557/50000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4790397658949187/50000000000000000000 : ℝ) ≤ ((3621012078388618703/3622000000000000000 : ℝ)+2*(258569788883/181100000000000 : ℝ)*(11143/100000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (3621012078388618703/3622000000000000000 : ℝ)+2*(258569788883/181100000000000 : ℝ)*(11143/100000 : ℝ)=(10000454377834423/10000000000000000 : ℝ) by norm_num, show 1+2*(4790397658949187/50000000000000000000 : ℝ)=(25004790397658949187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31392522456272557/100000000000000000000 : ℝ)+(4790397658949187/50000000000000000000 : ℝ) ≤ ((3621012078388618703/3622000000000000000 : ℝ)+(258569788883/181100000000000 : ℝ)*((2953/20000 : ℝ)+(11143/100000 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (3621012078388618703/3622000000000000000 : ℝ)+(258569788883/181100000000000 : ℝ)*((2953/20000 : ℝ)+(11143/100000 : ℝ))=(10000971517412189/10000000000000000 : ℝ) by norm_num, show 1+(31392522456272557/100000000000000000000 : ℝ)+(4790397658949187/50000000000000000000 : ℝ)=(100040973317774170931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31392522456272557/100000000000000000000 : ℝ) ≤ ((3621012078388618703/3622000000000000000 : ℝ)+2*(258569788883/181100000000000 : ℝ)*(2953/20000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (3621012078388618703/3622000000000000000 : ℝ)+2*(258569788883/181100000000000 : ℝ)*(2953/20000 : ℝ)=(2000297731397991/2000000000000000 : ℝ) by norm_num, show 1+2*(31392522456272557/100000000000000000000 : ℝ)=(50031392522456272557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3621012078388618703/3622000000000000000 : ℝ)*(X 1 0+X 2 0)+(258569788883/181100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (3621012078388618703/3622000000000000000 : ℝ)) (alpha := (258569788883/181100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3621012078388618703/3622000000000000000 : ℝ)*(X 0 1+X 2 1)+(258569788883/181100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (3621012078388618703/3622000000000000000 : ℝ)) (alpha := (258569788883/181100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3621012078388618703/3622000000000000000 : ℝ)*(X 0 2+X 1 2)+(258569788883/181100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (3621012078388618703/3622000000000000000 : ℝ)) (alpha := (258569788883/181100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2029336699/10000000000 : ℝ)*X 0 0+(5412163411/10000000000 : ℝ)*X 0 1+(5244807253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674391703/5000000000 : ℝ)*X 1 0+(-2114598489/10000000000 : ℝ)*X 1 1+(1048961457/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348783407/10000000000 : ℝ)*X 2 0+(5244807297/10000000000 : ℝ)*X 2 1+(-2114598471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540271329/1250000000 : ℝ)*X 0 0+(259319853/625000000 : ℝ)*X 0 1+(900380121/2000000000 : ℝ)*X 0 2+(540271329/1250000000 : ℝ)*X 1 0+(259319853/625000000 : ℝ)*X 1 1+(900380121/2000000000 : ℝ)*X 1 2+(540271329/1250000000 : ℝ)*X 2 0+(259319853/625000000 : ℝ)*X 2 1+(900380121/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1014674299/5000000000 : ℝ)*X 0 0+(1311352469/2500000000 : ℝ)*X 0 1+(676444731/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305592569/10000000000 : ℝ)*X 1 0+(-97392399/500000000 : ℝ)*X 1 1+(338222393/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2072497/3906250 : ℝ)*X 2 0+(2705779313/5000000000 : ℝ)*X 2 1+(-389569571/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322195991/10000000000 : ℝ)*X 0 0+(4500631227/10000000000 : ℝ)*X 0 1+(1037598457/2500000000 : ℝ)*X 0 2+(4322195991/10000000000 : ℝ)*X 1 0+(4500631227/10000000000 : ℝ)*X 1 1+(1037598457/2500000000 : ℝ)*X 1 2+(4322195991/10000000000 : ℝ)*X 2 0+(4500631227/10000000000 : ℝ)*X 2 1+(1037598457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (288365974366772435252193621/90550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31116671/5000000000000 : ℝ)*(base19) + (293291261/50000000000000 : ℝ)*(base23) + (45469173/50000000000000 : ℝ)*(upper3) + (1971991/10000000000000 : ℝ)*(upper4) + (1352671/1562500000000 : ℝ)*(upper5) + (2202480864186969/50000000000000 : ℝ)*(major0) + (2202480864186969/50000000000000 : ℝ)*(major1) + (2202480864186969/50000000000000 : ℝ)*(major2) + (2987646795816441/50000000000000 : ℝ)*(sp0) + (373456650586357/6250000000000 : ℝ)*(sp1) + (597530644513261/10000000000000 : ℝ)*(sp2) + (2834610056520861/100000000000000 : ℝ)*(sp3) + (53760329/400000000000 : ℝ)*(sp4) + (6262358381/100000000000000 : ℝ)*(sp7) + (1417308159439621/50000000000000 : ℝ)*(f.failure) + (1493826757928783/25000000000000 : ℝ)*(f.sum) + (54267875437479/9055000000000000000000000000 : ℝ)*base65 + (109182270613878793/181100000000000000000000000000000 : ℝ)*base68 + (1326026602036078793/181100000000000000000000000000000 : ℝ)*base70 + (1402771667880321207/181100000000000000000000000000000 : ℝ)*base71 + (1660355080331/9055000000000000000000000000 : ℝ)*base74 + (975322970207478793/181100000000000000000000000000000 : ℝ)*base76 + (1570370792077478793/181100000000000000000000000000000 : ℝ)*base78 + (804743648111321207/181100000000000000000000000000000 : ℝ)*base79 + (28857993790789/9055000000000000000000000000 : ℝ)*base81 + (3662827/500000000000000000000 : ℝ)*base89 + (3662827/500000000000000000000 : ℝ)*base91 + (3662827/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1126085246362228805733991881/90550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184725191/50000000000000 : ℝ)*(base19) + (114227783/25000000000000 : ℝ)*(base23) + (320772539/100000000000000 : ℝ)*(upper3) + (60708141/50000000000000 : ℝ)*(lower4) + (10404079/50000000000000 : ℝ)*(upper5) + (2218481391284703/50000000000000 : ℝ)*(major0) + (2218481391284703/50000000000000 : ℝ)*(major1) + (2218481391284703/50000000000000 : ℝ)*(major2) + (27243283/400000000000 : ℝ)*(sp1) + (4828280889/20000000000000 : ℝ)*(sp2) + (3009357991507331/50000000000000 : ℝ)*(sp4) + (6018708802743529/100000000000000 : ℝ)*(sp5) + (1203738276939817/20000000000000 : ℝ)*(sp6) + (713802291897201/25000000000000 : ℝ)*(sp7) + (713802291897201/25000000000000 : ℝ)*(f.failure) + (3009357991507331/50000000000000 : ℝ)*(f.sum) + (5008935513671/4527500000000000000000000000 : ℝ)*base66 + (2676461810543419791/181100000000000000000000000000000 : ℝ)*base68 + (2006787453918219791/181100000000000000000000000000000 : ℝ)*base70 + (656999564572919791/181100000000000000000000000000000 : ℝ)*base72 + (1859918029273/2263750000000000000000000000 : ℝ)*base74 + (29594650796819791/181100000000000000000000000000000 : ℝ)*base76 + (1537754207988319791/181100000000000000000000000000000 : ℝ)*base78 + (1680899053392719791/181100000000000000000000000000000 : ℝ)*base80 + (3396486115953/2263750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4156287/250000000000000000000 : ℝ)*base89 + (4156287/250000000000000000000 : ℝ)*base91 + (4156287/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1359_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1359_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1359_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1359_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1359_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1359_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
