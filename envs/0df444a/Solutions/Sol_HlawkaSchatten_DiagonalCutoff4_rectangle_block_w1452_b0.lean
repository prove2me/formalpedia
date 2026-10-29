-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1452_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:40.896021+00:00
-- url     : https://prove2.me/submissions/81bfd895-db86-4eb7-bac4-b771da06aff7

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
theorem support_rectangle_w1452_s0_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1745864839/10000000000 : ℝ)*x 0 + (5950747271/10000000000 : ℝ)*x 1 + (1209117141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1745864839/10000000000 : ℝ)^1103 ≤ (2575452132189/25000000000000 : ℝ)^847 := by
    have hnat : (1745864839 : ℕ)^1103*25000000000000^847 ≤ 2575452132189^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745864839 10000000000 2575452132189 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5950747271/10000000000 : ℝ)^1103 ≤ (50867134617249/100000000000000 : ℝ)^847 := by
    have hnat : (5950747271 : ℕ)^1103*100000000000000^847 ≤ 50867134617249^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5950747271 10000000000 50867134617249 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209117141/2500000000 : ℝ)^1103 ≤ (2426941052101/6250000000000 : ℝ)^847 := by
    have hnat : (1209117141 : ℕ)^1103*6250000000000^847 ≤ 2426941052101^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209117141 2500000000 2426941052101 6250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1745864839/10000000000 : ℝ), (5950747271/10000000000 : ℝ), (1209117141/2500000000 : ℝ)] ![(2575452132189/25000000000000 : ℝ), (50867134617249/100000000000000 : ℝ), (2426941052101/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1745864839/10000000000 : ℝ)|^1103 ≤ (2575452132189/25000000000000 : ℝ)^847
        have hw : |(-1745864839/10000000000 : ℝ)|=(1745864839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5950747271/10000000000 : ℝ)|^1103 ≤ (50867134617249/100000000000000 : ℝ)^847
        have hw : |(5950747271/10000000000 : ℝ)|=(5950747271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209117141/2500000000 : ℝ)|^1103 ≤ (2426941052101/6250000000000 : ℝ)^847
        have hw : |(1209117141/2500000000 : ℝ)|=(1209117141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s0_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (219581791/400000000 : ℝ)*x 0 + (-593580303/2500000000 : ℝ)*x 1 + (4836468449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219581791/400000000 : ℝ)^1103 ≤ (45794461467521/100000000000000 : ℝ)^847 := by
    have hnat : (219581791 : ℕ)^1103*100000000000000^847 ≤ 45794461467521^847*400000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219581791 400000000 45794461467521 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593580303/2500000000 : ℝ)^1103 ≤ (15374482882541/100000000000000 : ℝ)^847 := by
    have hnat : (593580303 : ℕ)^1103*100000000000000^847 ≤ 15374482882541^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593580303 2500000000 15374482882541 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4836468449/10000000000 : ℝ)^1103 ≤ (38831055631239/100000000000000 : ℝ)^847 := by
    have hnat : (4836468449 : ℕ)^1103*100000000000000^847 ≤ 38831055631239^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836468449 10000000000 38831055631239 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(219581791/400000000 : ℝ), (-593580303/2500000000 : ℝ), (4836468449/10000000000 : ℝ)] ![(45794461467521/100000000000000 : ℝ), (15374482882541/100000000000000 : ℝ), (38831055631239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(219581791/400000000 : ℝ)|^1103 ≤ (45794461467521/100000000000000 : ℝ)^847
        have hw : |(219581791/400000000 : ℝ)|=(219581791/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-593580303/2500000000 : ℝ)|^1103 ≤ (15374482882541/100000000000000 : ℝ)^847
        have hw : |(-593580303/2500000000 : ℝ)|=(593580303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4836468449/10000000000 : ℝ)|^1103 ≤ (38831055631239/100000000000000 : ℝ)^847
        have hw : |(4836468449/10000000000 : ℝ)|=(4836468449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s0_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1372386149/2500000000 : ℝ)*x 0 + (2418234209/5000000000 : ℝ)*x 1 + (-1187160741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372386149/2500000000 : ℝ)^1103 ≤ (45794459522959/100000000000000 : ℝ)^847 := by
    have hnat : (1372386149 : ℕ)^1103*100000000000000^847 ≤ 45794459522959^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372386149 2500000000 45794459522959 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418234209/5000000000 : ℝ)^1103 ≤ (38831055307119/100000000000000 : ℝ)^847 := by
    have hnat : (2418234209 : ℕ)^1103*100000000000000^847 ≤ 38831055307119^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418234209 5000000000 38831055307119 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187160741/5000000000 : ℝ)^1103 ≤ (15374485159299/100000000000000 : ℝ)^847 := by
    have hnat : (1187160741 : ℕ)^1103*100000000000000^847 ≤ 15374485159299^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187160741 5000000000 15374485159299 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1372386149/2500000000 : ℝ), (2418234209/5000000000 : ℝ), (-1187160741/5000000000 : ℝ)] ![(45794459522959/100000000000000 : ℝ), (38831055307119/100000000000000 : ℝ), (15374485159299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1372386149/2500000000 : ℝ)|^1103 ≤ (45794459522959/100000000000000 : ℝ)^847
        have hw : |(1372386149/2500000000 : ℝ)|=(1372386149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418234209/5000000000 : ℝ)|^1103 ≤ (38831055307119/100000000000000 : ℝ)^847
        have hw : |(2418234209/5000000000 : ℝ)|=(2418234209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1187160741/5000000000 : ℝ)|^1103 ≤ (15374485159299/100000000000000 : ℝ)^847
        have hw : |(-1187160741/5000000000 : ℝ)|=(1187160741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s0_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4162720017/10000000000 : ℝ)*x 0 + (3102859693/10000000000 : ℝ)*x 1 + (1383436523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162720017/10000000000 : ℝ)^1103 ≤ (31940120070599/100000000000000 : ℝ)^847 := by
    have hnat : (4162720017 : ℕ)^1103*100000000000000^847 ≤ 31940120070599^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162720017 10000000000 31940120070599 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102859693/10000000000 : ℝ)^1103 ≤ (4356931078027/20000000000000 : ℝ)^847 := by
    have hnat : (3102859693 : ℕ)^1103*20000000000000^847 ≤ 4356931078027^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102859693 10000000000 4356931078027 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383436523/2500000000 : ℝ)^1103 ≤ (11568806130811/25000000000000 : ℝ)^847 := by
    have hnat : (1383436523 : ℕ)^1103*25000000000000^847 ≤ 11568806130811^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383436523 2500000000 11568806130811 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162720017/10000000000 : ℝ), (3102859693/10000000000 : ℝ), (1383436523/2500000000 : ℝ)] ![(31940120070599/100000000000000 : ℝ), (4356931078027/20000000000000 : ℝ), (11568806130811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162720017/10000000000 : ℝ)|^1103 ≤ (31940120070599/100000000000000 : ℝ)^847
        have hw : |(4162720017/10000000000 : ℝ)|=(4162720017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102859693/10000000000 : ℝ)|^1103 ≤ (4356931078027/20000000000000 : ℝ)^847
        have hw : |(3102859693/10000000000 : ℝ)|=(3102859693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1383436523/2500000000 : ℝ)|^1103 ≤ (11568806130811/25000000000000 : ℝ)^847
        have hw : |(1383436523/2500000000 : ℝ)|=(1383436523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s0_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-174977327/1000000000 : ℝ)*x 0 + (4864926539/10000000000 : ℝ)*x 1 + (148031829/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174977327/1000000000 : ℝ)^1103 ≤ (10331851593429/100000000000000 : ℝ)^847 := by
    have hnat : (174977327 : ℕ)^1103*100000000000000^847 ≤ 10331851593429^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174977327 1000000000 10331851593429 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4864926539/10000000000 : ℝ)^1103 ≤ (39128862128871/100000000000000 : ℝ)^847 := by
    have hnat : (4864926539 : ℕ)^1103*100000000000000^847 ≤ 39128862128871^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4864926539 10000000000 39128862128871 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148031829/250000000 : ℝ)^1103 ≤ (315870539109/625000000000 : ℝ)^847 := by
    have hnat : (148031829 : ℕ)^1103*625000000000^847 ≤ 315870539109^847*250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148031829 250000000 315870539109 625000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174977327/1000000000 : ℝ), (4864926539/10000000000 : ℝ), (148031829/250000000 : ℝ)] ![(10331851593429/100000000000000 : ℝ), (39128862128871/100000000000000 : ℝ), (315870539109/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174977327/1000000000 : ℝ)|^1103 ≤ (10331851593429/100000000000000 : ℝ)^847
        have hw : |(-174977327/1000000000 : ℝ)|=(174977327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4864926539/10000000000 : ℝ)|^1103 ≤ (39128862128871/100000000000000 : ℝ)^847
        have hw : |(4864926539/10000000000 : ℝ)|=(4864926539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148031829/250000000 : ℝ)|^1103 ≤ (315870539109/625000000000 : ℝ)^847
        have hw : |(148031829/250000000 : ℝ)|=(148031829/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s0_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5185314999/10000000000 : ℝ)*x 0 + (-322379187/2500000000 : ℝ)*x 1 + (5921273229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185314999/10000000000 : ℝ)^1103 ≤ (21258757215807/50000000000000 : ℝ)^847 := by
    have hnat : (5185314999 : ℕ)^1103*50000000000000^847 ≤ 21258757215807^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185314999 10000000000 21258757215807 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322379187/2500000000 : ℝ)^1103 ≤ (173579963043/2500000000000 : ℝ)^847 := by
    have hnat : (322379187 : ℕ)^1103*2500000000000^847 ≤ 173579963043^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322379187 2500000000 173579963043 2500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5921273229/10000000000 : ℝ)^1103 ≤ (50539287024369/100000000000000 : ℝ)^847 := by
    have hnat : (5921273229 : ℕ)^1103*100000000000000^847 ≤ 50539287024369^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5921273229 10000000000 50539287024369 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185314999/10000000000 : ℝ), (-322379187/2500000000 : ℝ), (5921273229/10000000000 : ℝ)] ![(21258757215807/50000000000000 : ℝ), (173579963043/2500000000000 : ℝ), (50539287024369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185314999/10000000000 : ℝ)|^1103 ≤ (21258757215807/50000000000000 : ℝ)^847
        have hw : |(5185314999/10000000000 : ℝ)|=(5185314999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-322379187/2500000000 : ℝ)|^1103 ≤ (173579963043/2500000000000 : ℝ)^847
        have hw : |(-322379187/2500000000 : ℝ)|=(322379187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5921273229/10000000000 : ℝ)|^1103 ≤ (50539287024369/100000000000000 : ℝ)^847
        have hw : |(5921273229/10000000000 : ℝ)|=(5921273229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s0_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5185315031/10000000000 : ℝ)*x 0 + (2960636537/5000000000 : ℝ)*x 1 + (-644758473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185315031/10000000000 : ℝ)^1103 ≤ (21258757386653/50000000000000 : ℝ)^847 := by
    have hnat : (5185315031 : ℕ)^1103*50000000000000^847 ≤ 21258757386653^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185315031 10000000000 21258757386653 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2960636537/5000000000 : ℝ)^1103 ≤ (50539285301557/100000000000000 : ℝ)^847 := by
    have hnat : (2960636537 : ℕ)^1103*100000000000000^847 ≤ 50539285301557^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2960636537 5000000000 50539285301557 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644758473/5000000000 : ℝ)^1103 ≤ (6943199910041/100000000000000 : ℝ)^847 := by
    have hnat : (644758473 : ℕ)^1103*100000000000000^847 ≤ 6943199910041^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644758473 5000000000 6943199910041 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185315031/10000000000 : ℝ), (2960636537/5000000000 : ℝ), (-644758473/5000000000 : ℝ)] ![(21258757386653/50000000000000 : ℝ), (50539285301557/100000000000000 : ℝ), (6943199910041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185315031/10000000000 : ℝ)|^1103 ≤ (21258757386653/50000000000000 : ℝ)^847
        have hw : |(5185315031/10000000000 : ℝ)|=(5185315031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2960636537/5000000000 : ℝ)|^1103 ≤ (50539285301557/100000000000000 : ℝ)^847
        have hw : |(2960636537/5000000000 : ℝ)|=(2960636537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-644758473/5000000000 : ℝ)|^1103 ≤ (6943199910041/100000000000000 : ℝ)^847
        have hw : |(-644758473/5000000000 : ℝ)|=(644758473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s0_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2085622777/5000000000 : ℝ)*x 0 + (5471662329/10000000000 : ℝ)*x 1 + (197947503/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085622777/5000000000 : ℝ)^1103 ≤ (32025333397487/100000000000000 : ℝ)^847 := by
    have hnat : (2085622777 : ℕ)^1103*100000000000000^847 ≤ 32025333397487^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085622777 5000000000 32025333397487 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471662329/10000000000 : ℝ)^1103 ≤ (2280014584411/5000000000000 : ℝ)^847 := by
    have hnat : (5471662329 : ℕ)^1103*5000000000000^847 ≤ 2280014584411^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471662329 10000000000 2280014584411 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197947503/625000000 : ℝ)^1103 ≤ (894974996141/4000000000000 : ℝ)^847 := by
    have hnat : (197947503 : ℕ)^1103*4000000000000^847 ≤ 894974996141^847*625000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197947503 625000000 894974996141 4000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085622777/5000000000 : ℝ), (5471662329/10000000000 : ℝ), (197947503/625000000 : ℝ)] ![(32025333397487/100000000000000 : ℝ), (2280014584411/5000000000000 : ℝ), (894974996141/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085622777/5000000000 : ℝ)|^1103 ≤ (32025333397487/100000000000000 : ℝ)^847
        have hw : |(2085622777/5000000000 : ℝ)|=(2085622777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471662329/10000000000 : ℝ)|^1103 ≤ (2280014584411/5000000000000 : ℝ)^847
        have hw : |(5471662329/10000000000 : ℝ)|=(5471662329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197947503/625000000 : ℝ)|^1103 ≤ (894974996141/4000000000000 : ℝ)^847
        have hw : |(197947503/625000000 : ℝ)|=(197947503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2209/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (261/1000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4411/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4411 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4411*1^1024 ≤ 0^1024*1^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4411/1024 : ℝ) ≤ (48279947339048263/2500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4411 ≤ (48279947339048263/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4411*2500000000000000000^1024 ≤ 48279947339048263^1024*5^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 48279947339048263 2500000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (48279947339048263/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4411 := by
      have hnat : (1 : ℕ)^1024*1^4411 ≤ 1^4411*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2548279947339048263/2500000000000000000 : ℝ) ≤ (2511125872934567/2500000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (2548279947339048263/2500000000000000000 : ℝ)^1024 ≤ (2511125872934567/2500000000000000 : ℝ)^4411 := by
      have hnat : (2548279947339048263 : ℕ)^1024*2500000000000000^4411 ≤ 2511125872934567^4411*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2548279947339048263 2500000000000000000 2511125872934567 2500000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511125872934567/2500000000000000 : ℝ)) (X := (2548279947339048263/2500000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1298279947339048263/1250000000000000000 : ℝ) ≤ (1261125872934567/1250000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (1298279947339048263/1250000000000000000 : ℝ)^1024 ≤ (1261125872934567/1250000000000000 : ℝ)^4411 := by
      have hnat : (1298279947339048263 : ℕ)^1024*1250000000000000^4411 ≤ 1261125872934567^4411*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1298279947339048263 1250000000000000000 1261125872934567 1250000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261125872934567/1250000000000000 : ℝ)) (X := (1298279947339048263/1250000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11125872934567/1000000000000000 : ℝ)*(0 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11125872934567/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48279947339048263/2500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11125872934567/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11125872934567/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511125872934567/2500000000000000 : ℝ) by norm_num, show 1+(48279947339048263/2500000000000000000 : ℝ)+(0 : ℝ)=(2548279947339048263/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48279947339048263/2500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11125872934567/1000000000000000 : ℝ)*(2/5 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11125872934567/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261125872934567/1250000000000000 : ℝ) by norm_num, show 1+2*(48279947339048263/2500000000000000000 : ℝ)=(1298279947339048263/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11125872934567/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11125872934567/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11125872934567/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11125872934567/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11125872934567/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11125872934567/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1745864839/10000000000 : ℝ)*X 0 0+(5950747271/10000000000 : ℝ)*X 0 1+(1209117141/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((219581791/400000000 : ℝ)*X 1 0+(-593580303/2500000000 : ℝ)*X 1 1+(4836468449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1372386149/2500000000 : ℝ)*X 2 0+(2418234209/5000000000 : ℝ)*X 2 1+(-1187160741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4162720017/10000000000 : ℝ)*X 0 0+(3102859693/10000000000 : ℝ)*X 0 1+(1383436523/2500000000 : ℝ)*X 0 2+(4162720017/10000000000 : ℝ)*X 1 0+(3102859693/10000000000 : ℝ)*X 1 1+(1383436523/2500000000 : ℝ)*X 1 2+(4162720017/10000000000 : ℝ)*X 2 0+(3102859693/10000000000 : ℝ)*X 2 1+(1383436523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-174977327/1000000000 : ℝ)*X 0 0+(4864926539/10000000000 : ℝ)*X 0 1+(148031829/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185314999/10000000000 : ℝ)*X 1 0+(-322379187/2500000000 : ℝ)*X 1 1+(5921273229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185315031/10000000000 : ℝ)*X 2 0+(2960636537/5000000000 : ℝ)*X 2 1+(-644758473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2085622777/5000000000 : ℝ)*X 0 0+(5471662329/10000000000 : ℝ)*X 0 1+(197947503/625000000 : ℝ)*X 0 2+(2085622777/5000000000 : ℝ)*X 1 0+(5471662329/10000000000 : ℝ)*X 1 1+(197947503/625000000 : ℝ)*X 1 2+(2085622777/5000000000 : ℝ)*X 2 0+(5471662329/10000000000 : ℝ)*X 2 1+(197947503/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (167014466408932010224107/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69386871/50000000000000 : ℝ)*(base1) + (752569923/100000000000000 : ℝ)*(base19) + (45206659/6250000000000 : ℝ)*(base23) + (110854499/100000000000000 : ℝ)*(upper3) + (14534421/50000000000000 : ℝ)*(upper5) + (654410128108207/100000000000000 : ℝ)*(major0) + (654410128108207/100000000000000 : ℝ)*(major1) + (654410128108207/100000000000000 : ℝ)*(major2) + (224360966223871/25000000000000 : ℝ)*(sp0) + (22436120499009/2500000000000 : ℝ)*(sp1) + (897444849223739/100000000000000 : ℝ)*(sp2) + (4113733731441/1000000000000 : ℝ)*(sp3) + (1846408541/100000000000000 : ℝ)*(sp4) + (106042531/10000000000000 : ℝ)*(sp7) + (25710910771447/6250000000000 : ℝ)*(f.failure) + (897445572530283/100000000000000 : ℝ)*(f.sum) + (2324558008631/50000000000000000000000000000 : ℝ)*base66 + (284202998608631/100000000000000000000000000000 : ℝ)*base68 + (34322454908631/100000000000000000000000000000 : ℝ)*base70 + (130713162691369/100000000000000000000000000000 : ℝ)*base71 + (90010391808631/50000000000000000000000000000 : ℝ)*base74 + (81571834691369/100000000000000000000000000000 : ℝ)*base75 + (2988618291369/100000000000000000000000000000 : ℝ)*base77 + (127101112508631/100000000000000000000000000000 : ℝ)*base80 + (7636662591369/50000000000000000000000000000 : ℝ)*base81 + (104141/19531250000000000000 : ℝ)*base89 + (104141/19531250000000000000 : ℝ)*base91 + (104141/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11189936889749652821391/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205399933/25000000000000 : ℝ)*(base19) + (207303719/25000000000000 : ℝ)*(base23) + (102757103/100000000000000 : ℝ)*(base32) + (12682411/10000000000000 : ℝ)*(upper3) + (67014259/100000000000000 : ℝ)*(upper5) + (43143489483441/6250000000000 : ℝ)*(major0) + (43143489483441/6250000000000 : ℝ)*(major1) + (43143489483441/6250000000000 : ℝ)*(major2) + (495056623/25000000000000 : ℝ)*(sp1) + (1005224027/50000000000000 : ℝ)*(sp2) + (946658540367117/100000000000000 : ℝ)*(sp4) + (473327869270447/50000000000000 : ℝ)*(sp5) + (236663925176047/25000000000000 : ℝ)*(sp6) + (433932900986559/100000000000000 : ℝ)*(sp7) + (216966501871831/50000000000000 : ℝ)*(f.failure) + (946658540367117/100000000000000 : ℝ)*(f.sum) + (1193666455047/3125000000000000000000000000 : ℝ)*base65 + (16522535667547/6250000000000000000000000000 : ℝ)*base67 + (32081342944953/6250000000000000000000000000 : ℝ)*base70 + (26220608819953/6250000000000000000000000000 : ℝ)*base72 + (3211815989543/781250000000000000000000000 : ℝ)*base73 + (51813829907453/6250000000000000000000000000 : ℝ)*base76 + (33640718857453/6250000000000000000000000000 : ℝ)*base78 + (46901054463703/6250000000000000000000000000 : ℝ)*base80 + (7257529982453/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (561161/312500000000000000000 : ℝ)*base89 + (561161/312500000000000000000 : ℝ)*base91 + (561161/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1452_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (261/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1452_s1_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914972899/10000000000 : ℝ)*x 0 + (1399035559/2500000000 : ℝ)*x 1 + (5082622107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914972899/10000000000 : ℝ)^1103 ≤ (726241693657/6250000000000 : ℝ)^847 := by
    have hnat : (1914972899 : ℕ)^1103*6250000000000^847 ≤ 726241693657^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914972899 10000000000 726241693657 6250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1399035559/2500000000 : ℝ)^1103 ≤ (46955863212983/100000000000000 : ℝ)^847 := by
    have hnat : (1399035559 : ℕ)^1103*100000000000000^847 ≤ 46955863212983^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399035559 2500000000 46955863212983 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082622107/10000000000 : ℝ)^1103 ≤ (41424269666999/100000000000000 : ℝ)^847 := by
    have hnat : (5082622107 : ℕ)^1103*100000000000000^847 ≤ 41424269666999^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082622107 10000000000 41424269666999 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914972899/10000000000 : ℝ), (1399035559/2500000000 : ℝ), (5082622107/10000000000 : ℝ)] ![(726241693657/6250000000000 : ℝ), (46955863212983/100000000000000 : ℝ), (41424269666999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914972899/10000000000 : ℝ)|^1103 ≤ (726241693657/6250000000000 : ℝ)^847
        have hw : |(-1914972899/10000000000 : ℝ)|=(1914972899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1399035559/2500000000 : ℝ)|^1103 ≤ (46955863212983/100000000000000 : ℝ)^847
        have hw : |(1399035559/2500000000 : ℝ)|=(1399035559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5082622107/10000000000 : ℝ)|^1103 ≤ (41424269666999/100000000000000 : ℝ)^847
        have hw : |(5082622107/10000000000 : ℝ)|=(5082622107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s1_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (674314297/1250000000 : ℝ)*x 0 + (-437322207/2000000000 : ℝ)*x 1 + (5082623797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674314297/1250000000 : ℝ)^1103 ≤ (5595601613493/12500000000000 : ℝ)^847 := by
    have hnat : (674314297 : ℕ)^1103*12500000000000^847 ≤ 5595601613493^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674314297 1250000000 5595601613493 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437322207/2000000000 : ℝ)^1103 ≤ (1381089947427/10000000000000 : ℝ)^847 := by
    have hnat : (437322207 : ℕ)^1103*10000000000000^847 ≤ 1381089947427^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437322207 2000000000 1381089947427 10000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082623797/10000000000 : ℝ)^1103 ≤ (41424287603837/100000000000000 : ℝ)^847 := by
    have hnat : (5082623797 : ℕ)^1103*100000000000000^847 ≤ 41424287603837^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082623797 10000000000 41424287603837 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674314297/1250000000 : ℝ), (-437322207/2000000000 : ℝ), (5082623797/10000000000 : ℝ)] ![(5595601613493/12500000000000 : ℝ), (1381089947427/10000000000000 : ℝ), (41424287603837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674314297/1250000000 : ℝ)|^1103 ≤ (5595601613493/12500000000000 : ℝ)^847
        have hw : |(674314297/1250000000 : ℝ)|=(674314297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437322207/2000000000 : ℝ)|^1103 ≤ (1381089947427/10000000000000 : ℝ)^847
        have hw : |(-437322207/2000000000 : ℝ)|=(437322207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5082623797/10000000000 : ℝ)|^1103 ≤ (41424287603837/100000000000000 : ℝ)^847
        have hw : |(5082623797/10000000000 : ℝ)|=(5082623797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s1_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5394515763/10000000000 : ℝ)*x 0 + (5082622243/10000000000 : ℝ)*x 1 + (-2186611219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394515763/10000000000 : ℝ)^1103 ≤ (8952965579253/20000000000000 : ℝ)^847 := by
    have hnat : (5394515763 : ℕ)^1103*20000000000000^847 ≤ 8952965579253^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394515763 10000000000 8952965579253 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082622243/10000000000 : ℝ)^1103 ≤ (41424271110437/100000000000000 : ℝ)^847 := by
    have hnat : (5082622243 : ℕ)^1103*100000000000000^847 ≤ 41424271110437^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082622243 10000000000 41424271110437 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186611219/10000000000 : ℝ)^1103 ≤ (13810900987693/100000000000000 : ℝ)^847 := by
    have hnat : (2186611219 : ℕ)^1103*100000000000000^847 ≤ 13810900987693^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186611219 10000000000 13810900987693 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394515763/10000000000 : ℝ), (5082622243/10000000000 : ℝ), (-2186611219/10000000000 : ℝ)] ![(8952965579253/20000000000000 : ℝ), (41424271110437/100000000000000 : ℝ), (13810900987693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394515763/10000000000 : ℝ)|^1103 ≤ (8952965579253/20000000000000 : ℝ)^847
        have hw : |(5394515763/10000000000 : ℝ)|=(5394515763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082622243/10000000000 : ℝ)|^1103 ≤ (41424271110437/100000000000000 : ℝ)^847
        have hw : |(5082622243/10000000000 : ℝ)|=(5082622243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186611219/10000000000 : ℝ)|^1103 ≤ (13810900987693/100000000000000 : ℝ)^847
        have hw : |(-2186611219/10000000000 : ℝ)|=(2186611219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s1_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (854490261/2000000000 : ℝ)*x 0 + (3744772951/10000000000 : ℝ)*x 1 + (304065851/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854490261/2000000000 : ℝ)^1103 ≤ (33040893931887/100000000000000 : ℝ)^847 := by
    have hnat : (854490261 : ℕ)^1103*100000000000000^847 ≤ 33040893931887^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854490261 2000000000 33040893931887 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3744772951/10000000000 : ℝ)^1103 ≤ (27828912913981/100000000000000 : ℝ)^847 := by
    have hnat : (3744772951 : ℕ)^1103*100000000000000^847 ≤ 27828912913981^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3744772951 10000000000 27828912913981 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304065851/625000000 : ℝ)^1103 ≤ (39130193140047/100000000000000 : ℝ)^847 := by
    have hnat : (304065851 : ℕ)^1103*100000000000000^847 ≤ 39130193140047^847*625000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304065851 625000000 39130193140047 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854490261/2000000000 : ℝ), (3744772951/10000000000 : ℝ), (304065851/625000000 : ℝ)] ![(33040893931887/100000000000000 : ℝ), (27828912913981/100000000000000 : ℝ), (39130193140047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854490261/2000000000 : ℝ)|^1103 ≤ (33040893931887/100000000000000 : ℝ)^847
        have hw : |(854490261/2000000000 : ℝ)|=(854490261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3744772951/10000000000 : ℝ)|^1103 ≤ (27828912913981/100000000000000 : ℝ)^847
        have hw : |(3744772951/10000000000 : ℝ)|=(3744772951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(304065851/625000000 : ℝ)|^1103 ≤ (39130193140047/100000000000000 : ℝ)^847
        have hw : |(304065851/625000000 : ℝ)|=(304065851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s1_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1915340707/10000000000 : ℝ)*x 0 + (5088535839/10000000000 : ℝ)*x 1 + (5590130083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915340707/10000000000 : ℝ)^1103 ≤ (11622773558891/100000000000000 : ℝ)^847 := by
    have hnat : (1915340707 : ℕ)^1103*100000000000000^847 ≤ 11622773558891^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915340707 10000000000 11622773558891 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088535839/10000000000 : ℝ)^1103 ≤ (8297409233913/20000000000000 : ℝ)^847 := by
    have hnat : (5088535839 : ℕ)^1103*20000000000000^847 ≤ 8297409233913^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088535839 10000000000 8297409233913 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5590130083/10000000000 : ℝ)^1103 ≤ (46890180258857/100000000000000 : ℝ)^847 := by
    have hnat : (5590130083 : ℕ)^1103*100000000000000^847 ≤ 46890180258857^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590130083 10000000000 46890180258857 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1915340707/10000000000 : ℝ), (5088535839/10000000000 : ℝ), (5590130083/10000000000 : ℝ)] ![(11622773558891/100000000000000 : ℝ), (8297409233913/20000000000000 : ℝ), (46890180258857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1915340707/10000000000 : ℝ)|^1103 ≤ (11622773558891/100000000000000 : ℝ)^847
        have hw : |(-1915340707/10000000000 : ℝ)|=(1915340707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088535839/10000000000 : ℝ)|^1103 ≤ (8297409233913/20000000000000 : ℝ)^847
        have hw : |(5088535839/10000000000 : ℝ)|=(5088535839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5590130083/10000000000 : ℝ)|^1103 ≤ (46890180258857/100000000000000 : ℝ)^847
        have hw : |(5590130083/10000000000 : ℝ)|=(5590130083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s1_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5260120899/10000000000 : ℝ)*x 0 + (-167910409/1000000000 : ℝ)*x 1 + (1397532529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260120899/10000000000 : ℝ)^1103 ≤ (346544144789/800000000000 : ℝ)^847 := by
    have hnat : (5260120899 : ℕ)^1103*800000000000^847 ≤ 346544144789^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260120899 10000000000 346544144789 800000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167910409/1000000000 : ℝ)^1103 ≤ (489590063531/5000000000000 : ℝ)^847 := by
    have hnat : (167910409 : ℕ)^1103*5000000000000^847 ≤ 489590063531^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167910409 1000000000 489590063531 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1397532529/2500000000 : ℝ)^1103 ≤ (1875607224773/4000000000000 : ℝ)^847 := by
    have hnat : (1397532529 : ℕ)^1103*4000000000000^847 ≤ 1875607224773^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397532529 2500000000 1875607224773 4000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260120899/10000000000 : ℝ), (-167910409/1000000000 : ℝ), (1397532529/2500000000 : ℝ)] ![(346544144789/800000000000 : ℝ), (489590063531/5000000000000 : ℝ), (1875607224773/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260120899/10000000000 : ℝ)|^1103 ≤ (346544144789/800000000000 : ℝ)^847
        have hw : |(5260120899/10000000000 : ℝ)|=(5260120899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-167910409/1000000000 : ℝ)|^1103 ≤ (489590063531/5000000000000 : ℝ)^847
        have hw : |(-167910409/1000000000 : ℝ)|=(167910409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1397532529/2500000000 : ℝ)|^1103 ≤ (1875607224773/4000000000000 : ℝ)^847
        have hw : |(1397532529/2500000000 : ℝ)|=(1397532529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s1_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5260120797/10000000000 : ℝ)*x 0 + (5590130077/10000000000 : ℝ)*x 1 + (-1679104289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260120797/10000000000 : ℝ)^1103 ≤ (10829504251189/25000000000000 : ℝ)^847 := by
    have hnat : (5260120797 : ℕ)^1103*25000000000000^847 ≤ 10829504251189^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260120797 10000000000 10829504251189 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5590130077/10000000000 : ℝ)^1103 ≤ (23445090096659/50000000000000 : ℝ)^847 := by
    have hnat : (5590130077 : ℕ)^1103*50000000000000^847 ≤ 23445090096659^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590130077 10000000000 23445090096659 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1679104289/10000000000 : ℝ)^1103 ≤ (1223975347731/12500000000000 : ℝ)^847 := by
    have hnat : (1679104289 : ℕ)^1103*12500000000000^847 ≤ 1223975347731^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679104289 10000000000 1223975347731 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260120797/10000000000 : ℝ), (5590130077/10000000000 : ℝ), (-1679104289/10000000000 : ℝ)] ![(10829504251189/25000000000000 : ℝ), (23445090096659/50000000000000 : ℝ), (1223975347731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260120797/10000000000 : ℝ)|^1103 ≤ (10829504251189/25000000000000 : ℝ)^847
        have hw : |(5260120797/10000000000 : ℝ)|=(5260120797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5590130077/10000000000 : ℝ)|^1103 ≤ (23445090096659/50000000000000 : ℝ)^847
        have hw : |(5590130077/10000000000 : ℝ)|=(5590130077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1679104289/10000000000 : ℝ)|^1103 ≤ (1223975347731/12500000000000 : ℝ)^847
        have hw : |(-1679104289/10000000000 : ℝ)|=(1679104289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s1_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534156787/1250000000 : ℝ)*x 0 + (4852153827/10000000000 : ℝ)*x 1 + (1878943199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534156787/1250000000 : ℝ)^1103 ≤ (33048980975429/100000000000000 : ℝ)^847 := by
    have hnat : (534156787 : ℕ)^1103*100000000000000^847 ≤ 33048980975429^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534156787 1250000000 33048980975429 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4852153827/10000000000 : ℝ)^1103 ≤ (9748783428141/25000000000000 : ℝ)^847 := by
    have hnat : (4852153827 : ℕ)^1103*25000000000000^847 ≤ 9748783428141^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4852153827 10000000000 9748783428141 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878943199/5000000000 : ℝ)^1103 ≤ (3494485663131/12500000000000 : ℝ)^847 := by
    have hnat : (1878943199 : ℕ)^1103*12500000000000^847 ≤ 3494485663131^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878943199 5000000000 3494485663131 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534156787/1250000000 : ℝ), (4852153827/10000000000 : ℝ), (1878943199/5000000000 : ℝ)] ![(33048980975429/100000000000000 : ℝ), (9748783428141/25000000000000 : ℝ), (3494485663131/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534156787/1250000000 : ℝ)|^1103 ≤ (33048980975429/100000000000000 : ℝ)^847
        have hw : |(534156787/1250000000 : ℝ)|=(534156787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4852153827/10000000000 : ℝ)|^1103 ≤ (9748783428141/25000000000000 : ℝ)^847
        have hw : |(4852153827/10000000000 : ℝ)|=(4852153827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1878943199/5000000000 : ℝ)|^1103 ≤ (3494485663131/12500000000000 : ℝ)^847
        have hw : |(1878943199/5000000000 : ℝ)|=(1878943199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (261/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3919/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2337/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (261/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (261/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (261/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (261/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (261/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (261/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2209/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (3684673499569/50000000000000000000 : ℝ) := by
    have hpowers : (2209/100000 : ℝ)^4411 ≤ (3684673499569/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2209 : ℕ)^4411*50000000000000000000^1024 ≤ 3684673499569^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2209 100000 3684673499569 50000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2209/100000 : ℝ)) (X := (3684673499569/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (261/1000 : ℝ) ^ (4411/1024 : ℝ) ≤ (306980382520461653/100000000000000000000 : ℝ) := by
    have hpowers : (261/1000 : ℝ)^4411 ≤ (306980382520461653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (261 : ℕ)^4411*100000000000000000000^1024 ≤ 306980382520461653^1024*1000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        261 1000 306980382520461653 100000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (261/1000 : ℝ)) (X := (306980382520461653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003684673499569/25000000000000000000 : ℝ) ≤ (10000000342154201/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (25000003684673499569/25000000000000000000 : ℝ)^1024 ≤ (10000000342154201/10000000000000000 : ℝ)^4411 := by
      have hnat : (25000003684673499569 : ℕ)^1024*10000000000000000^4411 ≤ 10000000342154201^4411*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003684673499569 25000000000000000000 10000000342154201 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000342154201/10000000000000000 : ℝ)) (X := (25000003684673499569/25000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100306987751867460791/100000000000000000000 : ℝ) ≤ (10007118241329583/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (100306987751867460791/100000000000000000000 : ℝ)^1024 ≤ (10007118241329583/10000000000000000 : ℝ)^4411 := by
      have hnat : (100306987751867460791 : ℕ)^1024*10000000000000000^4411 ≤ 10007118241329583^4411*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100306987751867460791 100000000000000000000 10007118241329583 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007118241329583/10000000000000000 : ℝ)) (X := (100306987751867460791/100000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50306980382520461653/50000000000000000000 : ℝ) ≤ (2002847228100993/2000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50306980382520461653/50000000000000000000 : ℝ)^1024 ≤ (2002847228100993/2000000000000000 : ℝ)^4411 := by
      have hnat : (50306980382520461653 : ℕ)^1024*2000000000000000^4411 ≤ 2002847228100993^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50306980382520461653 50000000000000000000 2002847228100993 2000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002847228100993/2000000000000000 : ℝ)) (X := (50306980382520461653/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3684673499569/50000000000000000000 : ℝ) ≤ ((47775712259169835683/47782000000000000000 : ℝ)+2*(3558949587691/1194550000000000 : ℝ)*(2209/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (47775712259169835683/47782000000000000000 : ℝ)+2*(3558949587691/1194550000000000 : ℝ)*(2209/100000 : ℝ)=(10000000342154201/10000000000000000 : ℝ) by norm_num, show 1+2*(3684673499569/50000000000000000000 : ℝ)=(25000003684673499569/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(306980382520461653/100000000000000000000 : ℝ)+(3684673499569/50000000000000000000 : ℝ) ≤ ((47775712259169835683/47782000000000000000 : ℝ)+(3558949587691/1194550000000000 : ℝ)*((261/1000 : ℝ)+(2209/100000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (47775712259169835683/47782000000000000000 : ℝ)+(3558949587691/1194550000000000 : ℝ)*((261/1000 : ℝ)+(2209/100000 : ℝ))=(10007118241329583/10000000000000000 : ℝ) by norm_num, show 1+(306980382520461653/100000000000000000000 : ℝ)+(3684673499569/50000000000000000000 : ℝ)=(100306987751867460791/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(306980382520461653/100000000000000000000 : ℝ) ≤ ((47775712259169835683/47782000000000000000 : ℝ)+2*(3558949587691/1194550000000000 : ℝ)*(261/1000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (47775712259169835683/47782000000000000000 : ℝ)+2*(3558949587691/1194550000000000 : ℝ)*(261/1000 : ℝ)=(2002847228100993/2000000000000000 : ℝ) by norm_num, show 1+2*(306980382520461653/100000000000000000000 : ℝ)=(50306980382520461653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47775712259169835683/47782000000000000000 : ℝ)*(X 1 0+X 2 0)+(3558949587691/1194550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (2209/100000 : ℝ)) (hi := (261/1000 : ℝ)) (c := (47775712259169835683/47782000000000000000 : ℝ)) (alpha := (3558949587691/1194550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47775712259169835683/47782000000000000000 : ℝ)*(X 0 1+X 2 1)+(3558949587691/1194550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (2209/100000 : ℝ)) (hi := (261/1000 : ℝ)) (c := (47775712259169835683/47782000000000000000 : ℝ)) (alpha := (3558949587691/1194550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47775712259169835683/47782000000000000000 : ℝ)*(X 0 2+X 1 2)+(3558949587691/1194550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (2209/100000 : ℝ)) (hi := (261/1000 : ℝ)) (c := (47775712259169835683/47782000000000000000 : ℝ)) (alpha := (3558949587691/1194550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1914972899/10000000000 : ℝ)*X 0 0+(1399035559/2500000000 : ℝ)*X 0 1+(5082622107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((674314297/1250000000 : ℝ)*X 1 0+(-437322207/2000000000 : ℝ)*X 1 1+(5082623797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394515763/10000000000 : ℝ)*X 2 0+(5082622243/10000000000 : ℝ)*X 2 1+(-2186611219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((854490261/2000000000 : ℝ)*X 0 0+(3744772951/10000000000 : ℝ)*X 0 1+(304065851/625000000 : ℝ)*X 0 2+(854490261/2000000000 : ℝ)*X 1 0+(3744772951/10000000000 : ℝ)*X 1 1+(304065851/625000000 : ℝ)*X 1 2+(854490261/2000000000 : ℝ)*X 2 0+(3744772951/10000000000 : ℝ)*X 2 1+(304065851/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1915340707/10000000000 : ℝ)*X 0 0+(5088535839/10000000000 : ℝ)*X 0 1+(5590130083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260120899/10000000000 : ℝ)*X 1 0+(-167910409/1000000000 : ℝ)*X 1 1+(1397532529/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5260120797/10000000000 : ℝ)*X 2 0+(5590130077/10000000000 : ℝ)*X 2 1+(-1679104289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534156787/1250000000 : ℝ)*X 0 0+(4852153827/10000000000 : ℝ)*X 0 1+(1878943199/5000000000 : ℝ)*X 0 2+(534156787/1250000000 : ℝ)*X 1 0+(4852153827/10000000000 : ℝ)*X 1 1+(1878943199/5000000000 : ℝ)*X 1 2+(534156787/1250000000 : ℝ)*X 2 0+(4852153827/10000000000 : ℝ)*X 2 1+(1878943199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7543591312557754883914998519/1194550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1023337543/100000000000000 : ℝ)*(base19) + (294795681/20000000000000 : ℝ)*(base23) + (97073389/100000000000000 : ℝ)*(upper3) + (27001249/100000000000000 : ℝ)*(upper4) + (20455509/25000000000000 : ℝ)*(upper5) + (710003549089969/50000000000000 : ℝ)*(major0) + (710003549089969/50000000000000 : ℝ)*(major1) + (710003549089969/50000000000000 : ℝ)*(major2) + (97367810197001/5000000000000 : ℝ)*(sp0) + (486842416994319/25000000000000 : ℝ)*(sp1) + (1947369217336413/100000000000000 : ℝ)*(sp2) + (223159491175379/25000000000000 : ℝ)*(sp3) + (7243687399/50000000000000 : ℝ)*(sp4) + (532984331/10000000000000 : ℝ)*(sp7) + (446321647272413/50000000000000 : ℝ)*(f.failure) + (973685345657409/50000000000000 : ℝ)*(f.sum) + (169791441401073/59727500000000000000000000000 : ℝ)*base65 + (13436052645051923827/2389100000000000000000000000000000 : ℝ)*base67 + (2029160934474276173/2389100000000000000000000000000000 : ℝ)*base70 + (6426560851661123827/2389100000000000000000000000000000 : ℝ)*base71 + (46497011249243/59727500000000000000000000000 : ℝ)*base73 + (10875918433756076173/2389100000000000000000000000000000 : ℝ)*base76 + (5043132564399823827/2389100000000000000000000000000000 : ℝ)*base77 + (23597936313127223827/2389100000000000000000000000000000 : ℝ)*base79 + (257279258618679/119455000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1793997/312500000000000000000 : ℝ)*base90 + (1793997/312500000000000000000 : ℝ)*base92 + (1793997/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1491219237428375289285345267/170650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1871320087/100000000000000 : ℝ)*(base19) + (1913338289/100000000000000 : ℝ)*(base23) + (114827611/50000000000000 : ℝ)*(upper3) + (20415077/50000000000000 : ℝ)*(lower4) + (36488143/20000000000000 : ℝ)*(upper5) + (726874004290819/50000000000000 : ℝ)*(major0) + (726874004290819/50000000000000 : ℝ)*(major1) + (726874004290819/50000000000000 : ℝ)*(major2) + (2372981711/20000000000000 : ℝ)*(sp1) + (2996088617/25000000000000 : ℝ)*(sp2) + (1993642257485337/100000000000000 : ℝ)*(sp4) + (398725704251339/20000000000000 : ℝ)*(sp5) + (1993628359792581/100000000000000 : ℝ)*(sp6) + (913853468395731/100000000000000 : ℝ)*(sp7) + (913853468395731/100000000000000 : ℝ)*(f.failure) + (1993642257485337/100000000000000 : ℝ)*(f.sum) + (27797419182217/17065000000000000000000000000 : ℝ)*base66 + (1218040384440664911/341300000000000000000000000000000 : ℝ)*base67 + (2608409679562964911/341300000000000000000000000000000 : ℝ)*base69 + (854125648145364911/341300000000000000000000000000000 : ℝ)*base71 + (7642070048071/8532500000000000000000000000 : ℝ)*base74 + (1426516112923764911/341300000000000000000000000000000 : ℝ)*base75 + (491903754747435089/341300000000000000000000000000000 : ℝ)*base78 + (1594714526712735089/341300000000000000000000000000000 : ℝ)*base80 + (74848326805483/17065000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1337939/625000000000000000000 : ℝ)*base90 + (1337939/625000000000000000000 : ℝ)*base92 + (1337939/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1452_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (261/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3919/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2337/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1452_s2_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946424441/10000000000 : ℝ)*x 0 + (2726578843/5000000000 : ℝ)*x 1 + (5205336309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946424441/10000000000 : ℝ)^1103 ≤ (5934504016209/50000000000000 : ℝ)^847 := by
    have hnat : (1946424441 : ℕ)^1103*50000000000000^847 ≤ 5934504016209^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946424441 10000000000 5934504016209 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726578843/5000000000 : ℝ)^1103 ≤ (5674945981117/12500000000000 : ℝ)^847 := by
    have hnat : (2726578843 : ℕ)^1103*12500000000000^847 ≤ 5674945981117^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726578843 5000000000 5674945981117 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205336309/10000000000 : ℝ)^1103 ≤ (42731424106399/100000000000000 : ℝ)^847 := by
    have hnat : (5205336309 : ℕ)^1103*100000000000000^847 ≤ 42731424106399^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205336309 10000000000 42731424106399 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946424441/10000000000 : ℝ), (2726578843/5000000000 : ℝ), (5205336309/10000000000 : ℝ)] ![(5934504016209/50000000000000 : ℝ), (5674945981117/12500000000000 : ℝ), (42731424106399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946424441/10000000000 : ℝ)|^1103 ≤ (5934504016209/50000000000000 : ℝ)^847
        have hw : |(-1946424441/10000000000 : ℝ)|=(1946424441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726578843/5000000000 : ℝ)|^1103 ≤ (5674945981117/12500000000000 : ℝ)^847
        have hw : |(2726578843/5000000000 : ℝ)|=(2726578843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205336309/10000000000 : ℝ)|^1103 ≤ (42731424106399/100000000000000 : ℝ)^847
        have hw : |(5205336309/10000000000 : ℝ)|=(5205336309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s2_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1071740821/2000000000 : ℝ)*x 0 + (-2073801531/10000000000 : ℝ)*x 1 + (1301334081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071740821/2000000000 : ℝ)^1103 ≤ (22189112815743/50000000000000 : ℝ)^847 := by
    have hnat : (1071740821 : ℕ)^1103*50000000000000^847 ≤ 22189112815743^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071740821 2000000000 22189112815743 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073801531/10000000000 : ℝ)^1103 ≤ (6445175042917/50000000000000 : ℝ)^847 := by
    have hnat : (2073801531 : ℕ)^1103*50000000000000^847 ≤ 6445175042917^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073801531 10000000000 6445175042917 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301334081/2500000000 : ℝ)^1103 ≤ (42731424266753/100000000000000 : ℝ)^847 := by
    have hnat : (1301334081 : ℕ)^1103*100000000000000^847 ≤ 42731424266753^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301334081 2500000000 42731424266753 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071740821/2000000000 : ℝ), (-2073801531/10000000000 : ℝ), (1301334081/2500000000 : ℝ)] ![(22189112815743/50000000000000 : ℝ), (6445175042917/50000000000000 : ℝ), (42731424266753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071740821/2000000000 : ℝ)|^1103 ≤ (22189112815743/50000000000000 : ℝ)^847
        have hw : |(1071740821/2000000000 : ℝ)|=(1071740821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073801531/10000000000 : ℝ)|^1103 ≤ (6445175042917/50000000000000 : ℝ)^847
        have hw : |(-2073801531/10000000000 : ℝ)|=(2073801531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301334081/2500000000 : ℝ)|^1103 ≤ (42731424266753/100000000000000 : ℝ)^847
        have hw : |(1301334081/2500000000 : ℝ)|=(1301334081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s2_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2679352141/5000000000 : ℝ)*x 0 + (2602668057/5000000000 : ℝ)*x 1 + (-2073801573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679352141/5000000000 : ℝ)^1103 ≤ (44378227540353/100000000000000 : ℝ)^847 := by
    have hnat : (2679352141 : ℕ)^1103*100000000000000^847 ≤ 44378227540353^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679352141 5000000000 44378227540353 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602668057/5000000000 : ℝ)^1103 ≤ (21365711010893/50000000000000 : ℝ)^847 := by
    have hnat : (2602668057 : ℕ)^1103*50000000000000^847 ≤ 21365711010893^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602668057 5000000000 21365711010893 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073801573/10000000000 : ℝ)^1103 ≤ (12890350425803/100000000000000 : ℝ)^847 := by
    have hnat : (2073801573 : ℕ)^1103*100000000000000^847 ≤ 12890350425803^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073801573 10000000000 12890350425803 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679352141/5000000000 : ℝ), (2602668057/5000000000 : ℝ), (-2073801573/10000000000 : ℝ)] ![(44378227540353/100000000000000 : ℝ), (21365711010893/50000000000000 : ℝ), (12890350425803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679352141/5000000000 : ℝ)|^1103 ≤ (44378227540353/100000000000000 : ℝ)^847
        have hw : |(2679352141/5000000000 : ℝ)|=(2679352141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602668057/5000000000 : ℝ)|^1103 ≤ (21365711010893/50000000000000 : ℝ)^847
        have hw : |(2602668057/5000000000 : ℝ)|=(2602668057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073801573/10000000000 : ℝ)|^1103 ≤ (12890350425803/100000000000000 : ℝ)^847
        have hw : |(-2073801573/10000000000 : ℝ)|=(2073801573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s2_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (429470573/1000000000 : ℝ)*x 0 + (2015973587/5000000000 : ℝ)*x 1 + (4572588843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429470573/1000000000 : ℝ)^1103 ≤ (33265191446353/100000000000000 : ℝ)^847 := by
    have hnat : (429470573 : ℕ)^1103*100000000000000^847 ≤ 33265191446353^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429470573 1000000000 33265191446353 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015973587/5000000000 : ℝ)^1103 ≤ (30639690202443/100000000000000 : ℝ)^847 := by
    have hnat : (2015973587 : ℕ)^1103*100000000000000^847 ≤ 30639690202443^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015973587 5000000000 30639690202443 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4572588843/10000000000 : ℝ)^1103 ≤ (36095118333659/100000000000000 : ℝ)^847 := by
    have hnat : (4572588843 : ℕ)^1103*100000000000000^847 ≤ 36095118333659^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572588843 10000000000 36095118333659 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429470573/1000000000 : ℝ), (2015973587/5000000000 : ℝ), (4572588843/10000000000 : ℝ)] ![(33265191446353/100000000000000 : ℝ), (30639690202443/100000000000000 : ℝ), (36095118333659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429470573/1000000000 : ℝ)|^1103 ≤ (33265191446353/100000000000000 : ℝ)^847
        have hw : |(429470573/1000000000 : ℝ)|=(429470573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015973587/5000000000 : ℝ)|^1103 ≤ (30639690202443/100000000000000 : ℝ)^847
        have hw : |(2015973587/5000000000 : ℝ)|=(2015973587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4572588843/10000000000 : ℝ)|^1103 ≤ (36095118333659/100000000000000 : ℝ)^847
        have hw : |(4572588843/10000000000 : ℝ)|=(4572588843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s2_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-486616311/2500000000 : ℝ)*x 0 + (520672343/1000000000 : ℝ)*x 1 + (5451759933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486616311/2500000000 : ℝ)^1103 ≤ (11869332045427/100000000000000 : ℝ)^847 := by
    have hnat : (486616311 : ℕ)^1103*100000000000000^847 ≤ 11869332045427^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486616311 2500000000 11869332045427 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520672343/1000000000 : ℝ)^1103 ≤ (42746253469861/100000000000000 : ℝ)^847 := by
    have hnat : (520672343 : ℕ)^1103*100000000000000^847 ≤ 42746253469861^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520672343 1000000000 42746253469861 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451759933/10000000000 : ℝ)^1103 ≤ (1815376578953/4000000000000 : ℝ)^847 := by
    have hnat : (5451759933 : ℕ)^1103*4000000000000^847 ≤ 1815376578953^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451759933 10000000000 1815376578953 4000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486616311/2500000000 : ℝ), (520672343/1000000000 : ℝ), (5451759933/10000000000 : ℝ)] ![(11869332045427/100000000000000 : ℝ), (42746253469861/100000000000000 : ℝ), (1815376578953/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486616311/2500000000 : ℝ)|^1103 ≤ (11869332045427/100000000000000 : ℝ)^847
        have hw : |(-486616311/2500000000 : ℝ)|=(486616311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520672343/1000000000 : ℝ)|^1103 ≤ (42746253469861/100000000000000 : ℝ)^847
        have hw : |(520672343/1000000000 : ℝ)|=(520672343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451759933/10000000000 : ℝ)|^1103 ≤ (1815376578953/4000000000000 : ℝ)^847
        have hw : |(5451759933/10000000000 : ℝ)|=(5451759933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s2_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (264706269/500000000 : ℝ)*x 0 + (-114211017/625000000 : ℝ)*x 1 + (2725880671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264706269/500000000 : ℝ)^1103 ≤ (1092076118053/2500000000000 : ℝ)^847 := by
    have hnat : (264706269 : ℕ)^1103*2500000000000^847 ≤ 1092076118053^847*500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264706269 500000000 1092076118053 2500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114211017/625000000 : ℝ)^1103 ≤ (10932525524989/100000000000000 : ℝ)^847 := by
    have hnat : (114211017 : ℕ)^1103*100000000000000^847 ≤ 10932525524989^847*625000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114211017 625000000 10932525524989 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725880671/5000000000 : ℝ)^1103 ≤ (45384429748541/100000000000000 : ℝ)^847 := by
    have hnat : (2725880671 : ℕ)^1103*100000000000000^847 ≤ 45384429748541^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725880671 5000000000 45384429748541 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264706269/500000000 : ℝ), (-114211017/625000000 : ℝ), (2725880671/5000000000 : ℝ)] ![(1092076118053/2500000000000 : ℝ), (10932525524989/100000000000000 : ℝ), (45384429748541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264706269/500000000 : ℝ)|^1103 ≤ (1092076118053/2500000000000 : ℝ)^847
        have hw : |(264706269/500000000 : ℝ)|=(264706269/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114211017/625000000 : ℝ)|^1103 ≤ (10932525524989/100000000000000 : ℝ)^847
        have hw : |(-114211017/625000000 : ℝ)|=(114211017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725880671/5000000000 : ℝ)|^1103 ≤ (45384429748541/100000000000000 : ℝ)^847
        have hw : |(2725880671/5000000000 : ℝ)|=(2725880671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s2_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2647062151/5000000000 : ℝ)*x 0 + (1090352143/2000000000 : ℝ)*x 1 + (-1827378631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647062151/5000000000 : ℝ)^1103 ≤ (21841516569447/50000000000000 : ℝ)^847 := by
    have hnat : (2647062151 : ℕ)^1103*50000000000000^847 ≤ 21841516569447^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647062151 5000000000 21841516569447 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090352143/2000000000 : ℝ)^1103 ≤ (22692211475673/50000000000000 : ℝ)^847 := by
    have hnat : (1090352143 : ℕ)^1103*50000000000000^847 ≤ 22692211475673^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090352143 2000000000 22692211475673 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1827378631/10000000000 : ℝ)^1103 ≤ (5466271951799/50000000000000 : ℝ)^847 := by
    have hnat : (1827378631 : ℕ)^1103*50000000000000^847 ≤ 5466271951799^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827378631 10000000000 5466271951799 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647062151/5000000000 : ℝ), (1090352143/2000000000 : ℝ), (-1827378631/10000000000 : ℝ)] ![(21841516569447/50000000000000 : ℝ), (22692211475673/50000000000000 : ℝ), (5466271951799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647062151/5000000000 : ℝ)|^1103 ≤ (21841516569447/50000000000000 : ℝ)^847
        have hw : |(2647062151/5000000000 : ℝ)|=(2647062151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090352143/2000000000 : ℝ)|^1103 ≤ (22692211475673/50000000000000 : ℝ)^847
        have hw : |(1090352143/2000000000 : ℝ)|=(1090352143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1827378631/10000000000 : ℝ)|^1103 ≤ (5466271951799/50000000000000 : ℝ)^847
        have hw : |(-1827378631/10000000000 : ℝ)|=(1827378631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s2_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1073699041/2500000000 : ℝ)*x 0 + (4569566241/10000000000 : ℝ)*x 1 + (806998821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073699041/2500000000 : ℝ)^1103 ≤ (33266103629071/100000000000000 : ℝ)^847 := by
    have hnat : (1073699041 : ℕ)^1103*100000000000000^847 ≤ 33266103629071^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073699041 2500000000 33266103629071 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4569566241/10000000000 : ℝ)^1103 ≤ (36064050140813/100000000000000 : ℝ)^847 := by
    have hnat : (4569566241 : ℕ)^1103*100000000000000^847 ≤ 36064050140813^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569566241 10000000000 36064050140813 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806998821/2000000000 : ℝ)^1103 ≤ (30669846210021/100000000000000 : ℝ)^847 := by
    have hnat : (806998821 : ℕ)^1103*100000000000000^847 ≤ 30669846210021^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806998821 2000000000 30669846210021 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073699041/2500000000 : ℝ), (4569566241/10000000000 : ℝ), (806998821/2000000000 : ℝ)] ![(33266103629071/100000000000000 : ℝ), (36064050140813/100000000000000 : ℝ), (30669846210021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073699041/2500000000 : ℝ)|^1103 ≤ (33266103629071/100000000000000 : ℝ)^847
        have hw : |(1073699041/2500000000 : ℝ)|=(1073699041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4569566241/10000000000 : ℝ)|^1103 ≤ (36064050140813/100000000000000 : ℝ)^847
        have hw : |(4569566241/10000000000 : ℝ)|=(4569566241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806998821/2000000000 : ℝ)|^1103 ≤ (30669846210021/100000000000000 : ℝ)^847
        have hw : |(806998821/2000000000 : ℝ)|=(806998821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2337/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3933/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2337/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3919/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2337/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3919/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2337/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3919/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2337/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3919/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2337/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3919/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2337/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3919/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3919/50000 : ℝ) ^ (4411/1024 : ℝ) ≤ (1724485584954807/100000000000000000000 : ℝ) := by
    have hpowers : (3919/50000 : ℝ)^4411 ≤ (1724485584954807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3919 : ℕ)^4411*100000000000000000000^1024 ≤ 1724485584954807^1024*50000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3919 50000 1724485584954807 100000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3919/50000 : ℝ)) (X := (1724485584954807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2337/12500 : ℝ) ^ (4411/1024 : ℝ) ≤ (18235269632767239/25000000000000000000 : ℝ) := by
    have hpowers : (2337/12500 : ℝ)^4411 ≤ (18235269632767239/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2337 : ℕ)^4411*25000000000000000000^1024 ≤ 18235269632767239^1024*12500^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2337 12500 18235269632767239 25000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2337/12500 : ℝ)) (X := (18235269632767239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001724485584954807/50000000000000000000 : ℝ) ≤ (10000080065738229/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50001724485584954807/50000000000000000000 : ℝ)^1024 ≤ (10000080065738229/10000000000000000 : ℝ)^4411 := by
      have hnat : (50001724485584954807 : ℕ)^1024*10000000000000000^4411 ≤ 10000080065738229^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001724485584954807 50000000000000000000 10000080065738229 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000080065738229/10000000000000000 : ℝ)) (X := (50001724485584954807/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074665564116023763/100000000000000000000 : ℝ) ≤ (5000866420651837/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (100074665564116023763/100000000000000000000 : ℝ)^1024 ≤ (5000866420651837/5000000000000000 : ℝ)^4411 := by
      have hnat : (100074665564116023763 : ℕ)^1024*5000000000000000^4411 ≤ 5000866420651837^4411*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074665564116023763 100000000000000000000 5000866420651837 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000866420651837/5000000000000000 : ℝ)) (X := (100074665564116023763/100000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518235269632767239/12500000000000000000 : ℝ) ≤ (10003385616869119/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (12518235269632767239/12500000000000000000 : ℝ)^1024 ≤ (10003385616869119/10000000000000000 : ℝ)^4411 := by
      have hnat : (12518235269632767239 : ℕ)^1024*10000000000000000^4411 ≤ 10003385616869119^4411*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518235269632767239 12500000000000000000 10003385616869119 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003385616869119/10000000000000000 : ℝ)) (X := (12518235269632767239/12500000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1724485584954807/100000000000000000000 : ℝ) ≤ ((54277480222010887331/54290000000000000000 : ℝ)+2*(330555113089/217160000000000 : ℝ)*(3919/50000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (54277480222010887331/54290000000000000000 : ℝ)+2*(330555113089/217160000000000 : ℝ)*(3919/50000 : ℝ)=(10000080065738229/10000000000000000 : ℝ) by norm_num, show 1+2*(1724485584954807/100000000000000000000 : ℝ)=(50001724485584954807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18235269632767239/25000000000000000000 : ℝ)+(1724485584954807/100000000000000000000 : ℝ) ≤ ((54277480222010887331/54290000000000000000 : ℝ)+(330555113089/217160000000000 : ℝ)*((2337/12500 : ℝ)+(3919/50000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (54277480222010887331/54290000000000000000 : ℝ)+(330555113089/217160000000000 : ℝ)*((2337/12500 : ℝ)+(3919/50000 : ℝ))=(5000866420651837/5000000000000000 : ℝ) by norm_num, show 1+(18235269632767239/25000000000000000000 : ℝ)+(1724485584954807/100000000000000000000 : ℝ)=(100074665564116023763/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18235269632767239/25000000000000000000 : ℝ) ≤ ((54277480222010887331/54290000000000000000 : ℝ)+2*(330555113089/217160000000000 : ℝ)*(2337/12500 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (54277480222010887331/54290000000000000000 : ℝ)+2*(330555113089/217160000000000 : ℝ)*(2337/12500 : ℝ)=(10003385616869119/10000000000000000 : ℝ) by norm_num, show 1+2*(18235269632767239/25000000000000000000 : ℝ)=(12518235269632767239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54277480222010887331/54290000000000000000 : ℝ)*(X 1 0+X 2 0)+(330555113089/217160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (3919/50000 : ℝ)) (hi := (2337/12500 : ℝ)) (c := (54277480222010887331/54290000000000000000 : ℝ)) (alpha := (330555113089/217160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54277480222010887331/54290000000000000000 : ℝ)*(X 0 1+X 2 1)+(330555113089/217160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (3919/50000 : ℝ)) (hi := (2337/12500 : ℝ)) (c := (54277480222010887331/54290000000000000000 : ℝ)) (alpha := (330555113089/217160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54277480222010887331/54290000000000000000 : ℝ)*(X 0 2+X 1 2)+(330555113089/217160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (3919/50000 : ℝ)) (hi := (2337/12500 : ℝ)) (c := (54277480222010887331/54290000000000000000 : ℝ)) (alpha := (330555113089/217160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1946424441/10000000000 : ℝ)*X 0 0+(2726578843/5000000000 : ℝ)*X 0 1+(5205336309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071740821/2000000000 : ℝ)*X 1 0+(-2073801531/10000000000 : ℝ)*X 1 1+(1301334081/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679352141/5000000000 : ℝ)*X 2 0+(2602668057/5000000000 : ℝ)*X 2 1+(-2073801573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((429470573/1000000000 : ℝ)*X 0 0+(2015973587/5000000000 : ℝ)*X 0 1+(4572588843/10000000000 : ℝ)*X 0 2+(429470573/1000000000 : ℝ)*X 1 0+(2015973587/5000000000 : ℝ)*X 1 1+(4572588843/10000000000 : ℝ)*X 1 2+(429470573/1000000000 : ℝ)*X 2 0+(2015973587/5000000000 : ℝ)*X 2 1+(4572588843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-486616311/2500000000 : ℝ)*X 0 0+(520672343/1000000000 : ℝ)*X 0 1+(5451759933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264706269/500000000 : ℝ)*X 1 0+(-114211017/625000000 : ℝ)*X 1 1+(2725880671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647062151/5000000000 : ℝ)*X 2 0+(1090352143/2000000000 : ℝ)*X 2 1+(-1827378631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1073699041/2500000000 : ℝ)*X 0 0+(4569566241/10000000000 : ℝ)*X 0 1+(806998821/2000000000 : ℝ)*X 0 2+(1073699041/2500000000 : ℝ)*X 1 0+(4569566241/10000000000 : ℝ)*X 1 1+(806998821/2000000000 : ℝ)*X 1 2+(1073699041/2500000000 : ℝ)*X 2 0+(4569566241/10000000000 : ℝ)*X 2 1+(806998821/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7290000268561881839116423257/1357250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (606068377/50000000000000 : ℝ)*(base19) + (636231311/50000000000000 : ℝ)*(base23) + (39096153/100000000000000 : ℝ)*(lower2) + (165728361/100000000000000 : ℝ)*(upper3) + (11923733/12500000000000 : ℝ)*(upper5) + (1471217292940751/50000000000000 : ℝ)*(major0) + (1471217292940751/50000000000000 : ℝ)*(major1) + (1471217292940751/50000000000000 : ℝ)*(major2) + (2017590953305227/50000000000000 : ℝ)*(sp0) + (2017598899648253/50000000000000 : ℝ)*(sp1) + (2017598869485319/50000000000000 : ℝ)*(sp2) + (36993226175763/2000000000000 : ℝ)*(sp3) + (8552411403/50000000000000 : ℝ)*(sp4) + (2168125771/25000000000000 : ℝ)*(sp7) + (924834990645617/50000000000000 : ℝ)*(f.failure) + (201759950571663/5000000000000 : ℝ)*(f.sum) + (4023273197097/5429000000000000000000000000 : ℝ)*base65 + (14315447360056724419/2714500000000000000000000000000000 : ℝ)*base68 + (19135968113546275581/2714500000000000000000000000000000 : ℝ)*base69 + (309038010292275581/2714500000000000000000000000000000 : ℝ)*base71 + (21455112078443/5429000000000000000000000000 : ℝ)*base74 + (24804939994523724419/2714500000000000000000000000000000 : ℝ)*base76 + (18473074623695275581/2714500000000000000000000000000000 : ℝ)*base77 + (24419309341077275581/2714500000000000000000000000000000 : ℝ)*base79 + (2133121929451/1085800000000000000000000000 : ℝ)*base81 + (1275073/312500000000000000000 : ℝ)*base90 + (1275073/312500000000000000000 : ℝ)*base92 + (1275073/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54054111240315774636523299/3812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42242579/3125000000000 : ℝ)*(base19) + (894458049/100000000000000 : ℝ)*(base23) + (88552799/25000000000000 : ℝ)*(upper3) + (180841727/50000000000000 : ℝ)*(lower4) + (371979389366127/12500000000000 : ℝ)*(major0) + (371979389366127/12500000000000 : ℝ)*(major1) + (371979389366127/12500000000000 : ℝ)*(major2) + (33909546747/100000000000000 : ℝ)*(sp1) + (8536614483/100000000000000 : ℝ)*(sp2) + (1554654319/25000000000000 : ℝ)*(sp3) + (2040501786131383/50000000000000 : ℝ)*(sp4) + (1020242077738373/25000000000000 : ℝ)*(sp5) + (2040497070595117/50000000000000 : ℝ)*(sp6) + (935329983186867/50000000000000 : ℝ)*(sp7) + (187066618499101/10000000000000 : ℝ)*(f.failure) + (2040501786131383/50000000000000 : ℝ)*(f.sum) + (3128320109/15250000000000000000000000 : ℝ)*base65 + (6028330911513067/7625000000000000000000000000000 : ℝ)*base68 + (59973262436263067/7625000000000000000000000000000 : ℝ)*base70 + (32596667053138067/7625000000000000000000000000000 : ℝ)*base72 + (22673806149/61000000000000000000000000 : ℝ)*base74 + (41323195743013067/7625000000000000000000000000000 : ℝ)*base76 + (5340304419486933/7625000000000000000000000000000 : ℝ)*base77 + (78842578024486933/7625000000000000000000000000000 : ℝ)*base79 + (191871817317/61000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (254531/62500000000000000000 : ℝ)*base89 + (254531/62500000000000000000 : ℝ)*base91 + (254531/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1452_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2337/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3933/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1452_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3933/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1452_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1452_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1452_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3933/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1452_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
