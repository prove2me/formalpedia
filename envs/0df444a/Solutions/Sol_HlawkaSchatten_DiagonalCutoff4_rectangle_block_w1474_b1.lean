-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:39.903313+00:00
-- url     : https://prove2.me/submissions/4bffba5a-43a7-48fd-afb4-bdceb6927430

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
theorem support_rectangle_w1474_s3_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-962435711/5000000000 : ℝ)*x 0 + (544326037/1000000000 : ℝ)*x 1 + (1302737447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962435711/5000000000 : ℝ)^4445 ≤ (11754478115729/100000000000000 : ℝ)^3421 := by
    have hnat : (962435711 : ℕ)^4445*100000000000000^3421 ≤ 11754478115729^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962435711 5000000000 11754478115729 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544326037/1000000000 : ℝ)^4445 ≤ (45372679547503/100000000000000 : ℝ)^3421 := by
    have hnat : (544326037 : ℕ)^4445*100000000000000^3421 ≤ 45372679547503^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544326037 1000000000 45372679547503 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302737447/2500000000 : ℝ)^4445 ≤ (10718210582621/25000000000000 : ℝ)^3421 := by
    have hnat : (1302737447 : ℕ)^4445*25000000000000^3421 ≤ 10718210582621^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302737447 2500000000 10718210582621 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-962435711/5000000000 : ℝ), (544326037/1000000000 : ℝ), (1302737447/2500000000 : ℝ)] ![(11754478115729/100000000000000 : ℝ), (45372679547503/100000000000000 : ℝ), (10718210582621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-962435711/5000000000 : ℝ)|^4445 ≤ (11754478115729/100000000000000 : ℝ)^3421
        have hw : |(-962435711/5000000000 : ℝ)|=(962435711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544326037/1000000000 : ℝ)|^4445 ≤ (45372679547503/100000000000000 : ℝ)^3421
        have hw : |(544326037/1000000000 : ℝ)|=(544326037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1302737447/2500000000 : ℝ)|^4445 ≤ (10718210582621/25000000000000 : ℝ)^3421
        have hw : |(1302737447/2500000000 : ℝ)|=(1302737447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s3_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167341321/312500000 : ℝ)*x 0 + (-408813991/2000000000 : ℝ)*x 1 + (5210949863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167341321/312500000 : ℝ)^4445 ≤ (44418254370881/100000000000000 : ℝ)^3421 := by
    have hnat : (167341321 : ℕ)^4445*100000000000000^3421 ≤ 44418254370881^3421*312500000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167341321 312500000 44418254370881 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408813991/2000000000 : ℝ)^4445 ≤ (1588612810351/12500000000000 : ℝ)^3421 := by
    have hnat : (408813991 : ℕ)^4445*12500000000000^3421 ≤ 1588612810351^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408813991 2000000000 1588612810351 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5210949863/10000000000 : ℝ)^4445 ≤ (21436421566123/50000000000000 : ℝ)^3421 := by
    have hnat : (5210949863 : ℕ)^4445*50000000000000^3421 ≤ 21436421566123^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210949863 10000000000 21436421566123 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167341321/312500000 : ℝ), (-408813991/2000000000 : ℝ), (5210949863/10000000000 : ℝ)] ![(44418254370881/100000000000000 : ℝ), (1588612810351/12500000000000 : ℝ), (21436421566123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167341321/312500000 : ℝ)|^4445 ≤ (44418254370881/100000000000000 : ℝ)^3421
        have hw : |(167341321/312500000 : ℝ)|=(167341321/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408813991/2000000000 : ℝ)|^4445 ≤ (1588612810351/12500000000000 : ℝ)^3421
        have hw : |(-408813991/2000000000 : ℝ)|=(408813991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5210949863/10000000000 : ℝ)|^4445 ≤ (21436421566123/50000000000000 : ℝ)^3421
        have hw : |(5210949863/10000000000 : ℝ)|=(5210949863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s3_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338730633/2500000000 : ℝ)*x 0 + (5210949633/10000000000 : ℝ)*x 1 + (-2044069913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338730633/2500000000 : ℝ)^4445 ≤ (44418257173089/100000000000000 : ℝ)^3421 := by
    have hnat : (1338730633 : ℕ)^4445*100000000000000^3421 ≤ 44418257173089^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338730633 2500000000 44418257173089 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5210949633/10000000000 : ℝ)^4445 ≤ (4287284067351/10000000000000 : ℝ)^3421 := by
    have hnat : (5210949633 : ℕ)^4445*10000000000000^3421 ≤ 4287284067351^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210949633 10000000000 4287284067351 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044069913/10000000000 : ℝ)^4445 ≤ (1270890214351/10000000000000 : ℝ)^3421 := by
    have hnat : (2044069913 : ℕ)^4445*10000000000000^3421 ≤ 1270890214351^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044069913 10000000000 1270890214351 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338730633/2500000000 : ℝ), (5210949633/10000000000 : ℝ), (-2044069913/10000000000 : ℝ)] ![(44418257173089/100000000000000 : ℝ), (4287284067351/10000000000000 : ℝ), (1270890214351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338730633/2500000000 : ℝ)|^4445 ≤ (44418257173089/100000000000000 : ℝ)^3421
        have hw : |(1338730633/2500000000 : ℝ)|=(1338730633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5210949633/10000000000 : ℝ)|^4445 ≤ (4287284067351/10000000000000 : ℝ)^3421
        have hw : |(5210949633/10000000000 : ℝ)|=(5210949633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2044069913/10000000000 : ℝ)|^4445 ≤ (1270890214351/10000000000000 : ℝ)^3421
        have hw : |(-2044069913/10000000000 : ℝ)|=(2044069913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s3_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143659479/5000000000 : ℝ)*x 0 + (1009420229/2500000000 : ℝ)*x 1 + (2275195141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143659479/5000000000 : ℝ)^4445 ≤ (33272759491421/100000000000000 : ℝ)^3421 := by
    have hnat : (2143659479 : ℕ)^4445*100000000000000^3421 ≤ 33272759491421^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143659479 5000000000 33272759491421 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009420229/2500000000 : ℝ)^4445 ≤ (15388858367897/50000000000000 : ℝ)^3421 := by
    have hnat : (1009420229 : ℕ)^4445*50000000000000^3421 ≤ 15388858367897^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009420229 2500000000 15388858367897 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275195141/5000000000 : ℝ)^4445 ≤ (7189904751799/20000000000000 : ℝ)^3421 := by
    have hnat : (2275195141 : ℕ)^4445*20000000000000^3421 ≤ 7189904751799^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275195141 5000000000 7189904751799 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143659479/5000000000 : ℝ), (1009420229/2500000000 : ℝ), (2275195141/5000000000 : ℝ)] ![(33272759491421/100000000000000 : ℝ), (15388858367897/50000000000000 : ℝ), (7189904751799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143659479/5000000000 : ℝ)|^4445 ≤ (33272759491421/100000000000000 : ℝ)^3421
        have hw : |(2143659479/5000000000 : ℝ)|=(2143659479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1009420229/2500000000 : ℝ)|^4445 ≤ (15388858367897/50000000000000 : ℝ)^3421
        have hw : |(1009420229/2500000000 : ℝ)|=(1009420229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2275195141/5000000000 : ℝ)|^4445 ≤ (7189904751799/20000000000000 : ℝ)^3421
        have hw : |(2275195141/5000000000 : ℝ)|=(2275195141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s3_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1924906167/10000000000 : ℝ)*x 0 + (5212187597/10000000000 : ℝ)*x 1 + (217680523/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1924906167/10000000000 : ℝ)^4445 ≤ (2350950760231/20000000000000 : ℝ)^3421 := by
    have hnat : (1924906167 : ℕ)^4445*20000000000000^3421 ≤ 2350950760231^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924906167 10000000000 2350950760231 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212187597/10000000000 : ℝ)^4445 ≤ (42886075173309/100000000000000 : ℝ)^3421 := by
    have hnat : (5212187597 : ℕ)^4445*100000000000000^3421 ≤ 42886075173309^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212187597 10000000000 42886075173309 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217680523/400000000 : ℝ)^4445 ≤ (22679585505561/50000000000000 : ℝ)^3421 := by
    have hnat : (217680523 : ℕ)^4445*50000000000000^3421 ≤ 22679585505561^3421*400000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217680523 400000000 22679585505561 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1924906167/10000000000 : ℝ), (5212187597/10000000000 : ℝ), (217680523/400000000 : ℝ)] ![(2350950760231/20000000000000 : ℝ), (42886075173309/100000000000000 : ℝ), (22679585505561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1924906167/10000000000 : ℝ)|^4445 ≤ (2350950760231/20000000000000 : ℝ)^3421
        have hw : |(-1924906167/10000000000 : ℝ)|=(1924906167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212187597/10000000000 : ℝ)|^4445 ≤ (42886075173309/100000000000000 : ℝ)^3421
        have hw : |(5212187597/10000000000 : ℝ)|=(5212187597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217680523/400000000 : ℝ)|^4445 ≤ (22679585505561/50000000000000 : ℝ)^3421
        have hw : |(217680523/400000000 : ℝ)|=(217680523/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s3_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294311069/10000000000 : ℝ)*x 0 + (-453251737/2500000000 : ℝ)*x 1 + (544201311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294311069/10000000000 : ℝ)^4445 ≤ (43766113185151/100000000000000 : ℝ)^3421 := by
    have hnat : (5294311069 : ℕ)^4445*100000000000000^3421 ≤ 43766113185151^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294311069 10000000000 43766113185151 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453251737/2500000000 : ℝ)^4445 ≤ (543735770569/5000000000000 : ℝ)^3421 := by
    have hnat : (453251737 : ℕ)^4445*5000000000000^3421 ≤ 543735770569^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453251737 2500000000 543735770569 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544201311/1000000000 : ℝ)^4445 ≤ (5669896423771/12500000000000 : ℝ)^3421 := by
    have hnat : (544201311 : ℕ)^4445*12500000000000^3421 ≤ 5669896423771^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544201311 1000000000 5669896423771 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294311069/10000000000 : ℝ), (-453251737/2500000000 : ℝ), (544201311/1000000000 : ℝ)] ![(43766113185151/100000000000000 : ℝ), (543735770569/5000000000000 : ℝ), (5669896423771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294311069/10000000000 : ℝ)|^4445 ≤ (43766113185151/100000000000000 : ℝ)^3421
        have hw : |(5294311069/10000000000 : ℝ)|=(5294311069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-453251737/2500000000 : ℝ)|^4445 ≤ (543735770569/5000000000000 : ℝ)^3421
        have hw : |(-453251737/2500000000 : ℝ)|=(453251737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544201311/1000000000 : ℝ)|^4445 ≤ (5669896423771/12500000000000 : ℝ)^3421
        have hw : |(544201311/1000000000 : ℝ)|=(544201311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s3_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647155553/5000000000 : ℝ)*x 0 + (2721006563/5000000000 : ℝ)*x 1 + (-2900811/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647155553/5000000000 : ℝ)^4445 ≤ (4376611358257/10000000000000 : ℝ)^3421 := by
    have hnat : (2647155553 : ℕ)^4445*10000000000000^3421 ≤ 4376611358257^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647155553 5000000000 4376611358257 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721006563/5000000000 : ℝ)^4445 ≤ (45359171563447/100000000000000 : ℝ)^3421 := by
    have hnat : (2721006563 : ℕ)^4445*100000000000000^3421 ≤ 45359171563447^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721006563 5000000000 45359171563447 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2900811/16000000 : ℝ)^4445 ≤ (679669677653/6250000000000 : ℝ)^3421 := by
    have hnat : (2900811 : ℕ)^4445*6250000000000^3421 ≤ 679669677653^3421*16000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2900811 16000000 679669677653 6250000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647155553/5000000000 : ℝ), (2721006563/5000000000 : ℝ), (-2900811/16000000 : ℝ)] ![(4376611358257/10000000000000 : ℝ), (45359171563447/100000000000000 : ℝ), (679669677653/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647155553/5000000000 : ℝ)|^4445 ≤ (4376611358257/10000000000000 : ℝ)^3421
        have hw : |(2647155553/5000000000 : ℝ)|=(2647155553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721006563/5000000000 : ℝ)|^4445 ≤ (45359171563447/100000000000000 : ℝ)^3421
        have hw : |(2721006563/5000000000 : ℝ)|=(2721006563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2900811/16000000 : ℝ)|^4445 ≤ (679669677653/6250000000000 : ℝ)^3421
        have hw : |(-2900811/16000000 : ℝ)|=(2900811/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s3_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071848863/2500000000 : ℝ)*x 0 + (1136914721/2500000000 : ℝ)*x 1 + (1010108351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071848863/2500000000 : ℝ)^4445 ≤ (33273530839227/100000000000000 : ℝ)^3421 := by
    have hnat : (1071848863 : ℕ)^4445*100000000000000^3421 ≤ 33273530839227^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071848863 2500000000 33273530839227 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136914721/2500000000 : ℝ)^4445 ≤ (35921488204529/100000000000000 : ℝ)^3421 := by
    have hnat : (1136914721 : ℕ)^4445*100000000000000^3421 ≤ 35921488204529^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136914721 2500000000 35921488204529 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010108351/2500000000 : ℝ)^4445 ≤ (30804980940159/100000000000000 : ℝ)^3421 := by
    have hnat : (1010108351 : ℕ)^4445*100000000000000^3421 ≤ 30804980940159^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010108351 2500000000 30804980940159 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071848863/2500000000 : ℝ), (1136914721/2500000000 : ℝ), (1010108351/2500000000 : ℝ)] ![(33273530839227/100000000000000 : ℝ), (35921488204529/100000000000000 : ℝ), (30804980940159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071848863/2500000000 : ℝ)|^4445 ≤ (33273530839227/100000000000000 : ℝ)^3421
        have hw : |(1071848863/2500000000 : ℝ)|=(1071848863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136914721/2500000000 : ℝ)|^4445 ≤ (35921488204529/100000000000000 : ℝ)^3421
        have hw : |(1136914721/2500000000 : ℝ)|=(1136914721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010108351/2500000000 : ℝ)|^4445 ≤ (30804980940159/100000000000000 : ℝ)^3421
        have hw : |(1010108351/2500000000 : ℝ)|=(1010108351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10663/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15579/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16159/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16159/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16159/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16159/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16159/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16159/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10131/100000 : ℝ) ^ (4443/1024 : ℝ) ≤ (484905888594163/10000000000000000000 : ℝ) := by
    have hpowers : (10131/100000 : ℝ)^4443 ≤ (484905888594163/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10131 : ℕ)^4443*10000000000000000000^1024 ≤ 484905888594163^1024*100000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10131 100000 484905888594163 10000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10131/100000 : ℝ)) (X := (484905888594163/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16159/100000 : ℝ) ^ (4443/1024 : ℝ) ≤ (36763391173911731/100000000000000000000 : ℝ) := by
    have hpowers : (16159/100000 : ℝ)^4443 ≤ (36763391173911731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16159 : ℕ)^4443*100000000000000000000^1024 ≤ 36763391173911731^1024*100000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16159 100000 36763391173911731 100000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16159/100000 : ℝ)) (X := (36763391173911731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000484905888594163/5000000000000000000 : ℝ) ≤ (10000223508936571/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (5000484905888594163/5000000000000000000 : ℝ)^1024 ≤ (10000223508936571/10000000000000000 : ℝ)^4443 := by
      have hnat : (5000484905888594163 : ℕ)^1024*10000000000000000^4443 ≤ 10000223508936571^4443*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000484905888594163 5000000000000000000 10000223508936571 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000223508936571/10000000000000000 : ℝ)) (X := (5000484905888594163/5000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041612450059853361/100000000000000000000 : ℝ) ≤ (5000479454513861/5000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (100041612450059853361/100000000000000000000 : ℝ)^1024 ≤ (5000479454513861/5000000000000000 : ℝ)^4443 := by
      have hnat : (100041612450059853361 : ℕ)^1024*5000000000000000^4443 ≤ 5000479454513861^4443*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041612450059853361 100000000000000000000 5000479454513861 5000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000479454513861/5000000000000000 : ℝ)) (X := (100041612450059853361/100000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036763391173911731/50000000000000000000 : ℝ) ≤ (10001694309118873/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (50036763391173911731/50000000000000000000 : ℝ)^1024 ≤ (10001694309118873/10000000000000000 : ℝ)^4443 := by
      have hnat : (50036763391173911731 : ℕ)^1024*10000000000000000^4443 ≤ 10001694309118873^4443*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036763391173911731 50000000000000000000 10001694309118873 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001694309118873/10000000000000000 : ℝ)) (X := (50036763391173911731/50000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(484905888594163/10000000000000000000 : ℝ) ≤ ((2739383937964670383/2740000000000000000 : ℝ)+2*(66854553741/54800000000000 : ℝ)*(10131/100000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (2739383937964670383/2740000000000000000 : ℝ)+2*(66854553741/54800000000000 : ℝ)*(10131/100000 : ℝ)=(10000223508936571/10000000000000000 : ℝ) by norm_num, show 1+2*(484905888594163/10000000000000000000 : ℝ)=(5000484905888594163/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36763391173911731/100000000000000000000 : ℝ)+(484905888594163/10000000000000000000 : ℝ) ≤ ((2739383937964670383/2740000000000000000 : ℝ)+(66854553741/54800000000000 : ℝ)*((16159/100000 : ℝ)+(10131/100000 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (2739383937964670383/2740000000000000000 : ℝ)+(66854553741/54800000000000 : ℝ)*((16159/100000 : ℝ)+(10131/100000 : ℝ))=(5000479454513861/5000000000000000 : ℝ) by norm_num, show 1+(36763391173911731/100000000000000000000 : ℝ)+(484905888594163/10000000000000000000 : ℝ)=(100041612450059853361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36763391173911731/100000000000000000000 : ℝ) ≤ ((2739383937964670383/2740000000000000000 : ℝ)+2*(66854553741/54800000000000 : ℝ)*(16159/100000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (2739383937964670383/2740000000000000000 : ℝ)+2*(66854553741/54800000000000 : ℝ)*(16159/100000 : ℝ)=(10001694309118873/10000000000000000 : ℝ) by norm_num, show 1+2*(36763391173911731/100000000000000000000 : ℝ)=(50036763391173911731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2739383937964670383/2740000000000000000 : ℝ)*(X 1 0+X 2 0)+(66854553741/54800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10131/100000 : ℝ)) (hi := (16159/100000 : ℝ)) (c := (2739383937964670383/2740000000000000000 : ℝ)) (alpha := (66854553741/54800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2739383937964670383/2740000000000000000 : ℝ)*(X 0 1+X 2 1)+(66854553741/54800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10131/100000 : ℝ)) (hi := (16159/100000 : ℝ)) (c := (2739383937964670383/2740000000000000000 : ℝ)) (alpha := (66854553741/54800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2739383937964670383/2740000000000000000 : ℝ)*(X 0 2+X 1 2)+(66854553741/54800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10131/100000 : ℝ)) (hi := (16159/100000 : ℝ)) (c := (2739383937964670383/2740000000000000000 : ℝ)) (alpha := (66854553741/54800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-962435711/5000000000 : ℝ)*X 0 0+(544326037/1000000000 : ℝ)*X 0 1+(1302737447/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167341321/312500000 : ℝ)*X 1 0+(-408813991/2000000000 : ℝ)*X 1 1+(5210949863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338730633/2500000000 : ℝ)*X 2 0+(5210949633/10000000000 : ℝ)*X 2 1+(-2044069913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2143659479/5000000000 : ℝ)*X 0 0+(1009420229/2500000000 : ℝ)*X 0 1+(2275195141/5000000000 : ℝ)*X 0 2+(2143659479/5000000000 : ℝ)*X 1 0+(1009420229/2500000000 : ℝ)*X 1 1+(2275195141/5000000000 : ℝ)*X 1 2+(2143659479/5000000000 : ℝ)*X 2 0+(1009420229/2500000000 : ℝ)*X 2 1+(2275195141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1924906167/10000000000 : ℝ)*X 0 0+(5212187597/10000000000 : ℝ)*X 0 1+(217680523/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294311069/10000000000 : ℝ)*X 1 0+(-453251737/2500000000 : ℝ)*X 1 1+(544201311/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647155553/5000000000 : ℝ)*X 2 0+(2721006563/5000000000 : ℝ)*X 2 1+(-2900811/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071848863/2500000000 : ℝ)*X 0 0+(1136914721/2500000000 : ℝ)*X 0 1+(1010108351/2500000000 : ℝ)*X 0 2+(1071848863/2500000000 : ℝ)*X 1 0+(1136914721/2500000000 : ℝ)*X 1 1+(1010108351/2500000000 : ℝ)*X 1 2+(1071848863/2500000000 : ℝ)*X 2 0+(1136914721/2500000000 : ℝ)*X 2 1+(1010108351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (313484098167846108359067477/34250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1044747053/50000000000000 : ℝ)*(base19) + (511999231/25000000000000 : ℝ)*(base23) + (13414227/10000000000000 : ℝ)*(lower2) + (241102741/100000000000000 : ℝ)*(upper3) + (63483257/50000000000000 : ℝ)*(upper5) + (781887818014509/25000000000000 : ℝ)*(major0) + (781887818014509/25000000000000 : ℝ)*(major1) + (781887818014509/25000000000000 : ℝ)*(major2) + (1076153978916597/25000000000000 : ℝ)*(sp0) + (2152324048031027/50000000000000 : ℝ)*(sp1) + (1076162034389809/25000000000000 : ℝ)*(sp2) + (975218049223249/50000000000000 : ℝ)*(sp3) + (34269889773/100000000000000 : ℝ)*(sp4) + (15955019393/100000000000000 : ℝ)*(sp7) + (487613013366473/25000000000000 : ℝ)*(f.failure) + (13452031829863/312500000000 : ℝ)*(f.sum) + (58829042683/85625000000000000000000000 : ℝ)*base65 + (195787819566536947/68500000000000000000000000000000 : ℝ)*base67 + (908462826105536947/68500000000000000000000000000000 : ℝ)*base69 + (556911751157036947/68500000000000000000000000000000 : ℝ)*base71 + (1073608448681/685000000000000000000000000 : ℝ)*base74 + (413297500620036947/68500000000000000000000000000000 : ℝ)*base75 + (564964688973036947/68500000000000000000000000000000 : ℝ)*base77 + (399864982297036947/68500000000000000000000000000000 : ℝ)*base79 + (1402743456269/685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (992007/312500000000000000000 : ℝ)*base89 + (992007/312500000000000000000 : ℝ)*base91 + (992007/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1192542784110053638482879897/137000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1248931653/100000000000000 : ℝ)*(base19) + (1519313847/100000000000000 : ℝ)*(base23) + (92275233/50000000000000 : ℝ)*(upper3) + (11870319/12500000000000 : ℝ)*(lower4) + (132931729/100000000000000 : ℝ)*(upper5) + (3161317687861053/100000000000000 : ℝ)*(major0) + (3161317687861053/100000000000000 : ℝ)*(major1) + (3161317687861053/100000000000000 : ℝ)*(major2) + (2163584469/12500000000000 : ℝ)*(sp1) + (282531303/1250000000000 : ℝ)*(sp2) + (2175562547967181/50000000000000 : ℝ)*(sp4) + (4351106538326957/100000000000000 : ℝ)*(sp5) + (174044038964651/4000000000000 : ℝ)*(sp6) + (123219374351959/6250000000000 : ℝ)*(sp7) + (123219374351959/6250000000000 : ℝ)*(f.failure) + (2175562547967181/50000000000000 : ℝ)*(f.sum) + (13846539876113/2740000000000000000000000000 : ℝ)*base65 + (3325964628056701/274000000000000000000000000000000 : ℝ)*base68 + (1556722361612056701/274000000000000000000000000000000 : ℝ)*base70 + (637829965101943299/274000000000000000000000000000000 : ℝ)*base71 + (10535812491273/2740000000000000000000000000 : ℝ)*base73 + (1203384317916056701/274000000000000000000000000000000 : ℝ)*base76 + (258711804220056701/274000000000000000000000000000000 : ℝ)*base78 + (2088208796427943299/274000000000000000000000000000000 : ℝ)*base79 + (1219230103667/2740000000000000000000000000 : ℝ)*base82 + (282369/78125000000000000000 : ℝ)*base90 + (282369/78125000000000000000 : ℝ)*base92 + (282369/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1474_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10663/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15579/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1474_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1474_s4_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7702179/40000000 : ℝ)*x 0 + (135972877/250000000 : ℝ)*x 1 + (1303712857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7702179/40000000 : ℝ)^4445 ≤ (11759820925691/100000000000000 : ℝ)^3421 := by
    have hnat : (7702179 : ℕ)^4445*100000000000000^3421 ≤ 11759820925691^3421*40000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7702179 40000000 11759820925691 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135972877/250000000 : ℝ)^4445 ≤ (45325622911559/100000000000000 : ℝ)^3421 := by
    have hnat : (135972877 : ℕ)^4445*100000000000000^3421 ≤ 45325622911559^3421*250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135972877 250000000 45325622911559 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303712857/2500000000 : ℝ)^4445 ≤ (21457278073667/50000000000000 : ℝ)^3421 := by
    have hnat : (1303712857 : ℕ)^4445*50000000000000^3421 ≤ 21457278073667^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303712857 2500000000 21457278073667 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7702179/40000000 : ℝ), (135972877/250000000 : ℝ), (1303712857/2500000000 : ℝ)] ![(11759820925691/100000000000000 : ℝ), (45325622911559/100000000000000 : ℝ), (21457278073667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7702179/40000000 : ℝ)|^4445 ≤ (11759820925691/100000000000000 : ℝ)^3421
        have hw : |(-7702179/40000000 : ℝ)|=(7702179/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135972877/250000000 : ℝ)|^4445 ≤ (45325622911559/100000000000000 : ℝ)^3421
        have hw : |(135972877/250000000 : ℝ)|=(135972877/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303712857/2500000000 : ℝ)|^4445 ≤ (21457278073667/50000000000000 : ℝ)^3421
        have hw : |(1303712857/2500000000 : ℝ)|=(1303712857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s4_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676898087/5000000000 : ℝ)*x 0 + (-408081637/2000000000 : ℝ)*x 1 + (5214851153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676898087/5000000000 : ℝ)^4445 ≤ (44406117980871/100000000000000 : ℝ)^3421 := by
    have hnat : (2676898087 : ℕ)^4445*100000000000000^3421 ≤ 44406117980871^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676898087 5000000000 44406117980871 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408081637/2000000000 : ℝ)^4445 ≤ (3169832197743/25000000000000 : ℝ)^3421 := by
    have hnat : (408081637 : ℕ)^4445*25000000000000^3421 ≤ 3169832197743^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408081637 2000000000 3169832197743 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214851153/10000000000 : ℝ)^4445 ≤ (21457276603441/50000000000000 : ℝ)^3421 := by
    have hnat : (5214851153 : ℕ)^4445*50000000000000^3421 ≤ 21457276603441^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214851153 10000000000 21457276603441 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676898087/5000000000 : ℝ), (-408081637/2000000000 : ℝ), (5214851153/10000000000 : ℝ)] ![(44406117980871/100000000000000 : ℝ), (3169832197743/25000000000000 : ℝ), (21457276603441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676898087/5000000000 : ℝ)|^4445 ≤ (44406117980871/100000000000000 : ℝ)^3421
        have hw : |(2676898087/5000000000 : ℝ)|=(2676898087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408081637/2000000000 : ℝ)|^4445 ≤ (3169832197743/25000000000000 : ℝ)^3421
        have hw : |(-408081637/2000000000 : ℝ)|=(408081637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214851153/10000000000 : ℝ)|^4445 ≤ (21457276603441/50000000000000 : ℝ)^3421
        have hw : |(5214851153/10000000000 : ℝ)|=(5214851153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s4_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535379603/1000000000 : ℝ)*x 0 + (5214851391/10000000000 : ℝ)*x 1 + (-1020204031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535379603/1000000000 : ℝ)^4445 ≤ (44406116428977/100000000000000 : ℝ)^3421 := by
    have hnat : (535379603 : ℕ)^4445*100000000000000^3421 ≤ 44406116428977^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535379603 1000000000 44406116428977 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214851391/10000000000 : ℝ)^4445 ≤ (42914555751709/100000000000000 : ℝ)^3421 := by
    have hnat : (5214851391 : ℕ)^4445*100000000000000^3421 ≤ 42914555751709^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214851391 10000000000 42914555751709 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020204031/5000000000 : ℝ)^4445 ≤ (12679327797849/100000000000000 : ℝ)^3421 := by
    have hnat : (1020204031 : ℕ)^4445*100000000000000^3421 ≤ 12679327797849^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020204031 5000000000 12679327797849 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535379603/1000000000 : ℝ), (5214851391/10000000000 : ℝ), (-1020204031/5000000000 : ℝ)] ![(44406116428977/100000000000000 : ℝ), (42914555751709/100000000000000 : ℝ), (12679327797849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535379603/1000000000 : ℝ)|^4445 ≤ (44406116428977/100000000000000 : ℝ)^3421
        have hw : |(535379603/1000000000 : ℝ)|=(535379603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214851391/10000000000 : ℝ)|^4445 ≤ (42914555751709/100000000000000 : ℝ)^3421
        have hw : |(5214851391/10000000000 : ℝ)|=(5214851391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020204031/5000000000 : ℝ)|^4445 ≤ (12679327797849/100000000000000 : ℝ)^3421
        have hw : |(-1020204031/5000000000 : ℝ)|=(1020204031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s4_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071934289/2500000000 : ℝ)*x 0 + (4046731707/10000000000 : ℝ)*x 1 + (2270620563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071934289/2500000000 : ℝ)^4445 ≤ (33276976553643/100000000000000 : ℝ)^3421 := by
    have hnat : (1071934289 : ℕ)^4445*100000000000000^3421 ≤ 33276976553643^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071934289 2500000000 33276976553643 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4046731707/10000000000 : ℝ)^4445 ≤ (15433694199877/50000000000000 : ℝ)^3421 := by
    have hnat : (4046731707 : ℕ)^4445*50000000000000^3421 ≤ 15433694199877^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046731707 10000000000 15433694199877 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270620563/5000000000 : ℝ)^4445 ≤ (3585563503223/10000000000000 : ℝ)^3421 := by
    have hnat : (2270620563 : ℕ)^4445*10000000000000^3421 ≤ 3585563503223^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270620563 5000000000 3585563503223 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071934289/2500000000 : ℝ), (4046731707/10000000000 : ℝ), (2270620563/5000000000 : ℝ)] ![(33276976553643/100000000000000 : ℝ), (15433694199877/50000000000000 : ℝ), (3585563503223/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071934289/2500000000 : ℝ)|^4445 ≤ (33276976553643/100000000000000 : ℝ)^3421
        have hw : |(1071934289/2500000000 : ℝ)|=(1071934289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4046731707/10000000000 : ℝ)|^4445 ≤ (15433694199877/50000000000000 : ℝ)^3421
        have hw : |(4046731707/10000000000 : ℝ)|=(4046731707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2270620563/5000000000 : ℝ)|^4445 ≤ (3585563503223/10000000000000 : ℝ)^3421
        have hw : |(2270620563/5000000000 : ℝ)|=(2270620563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s4_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925576357/10000000000 : ℝ)*x 0 + (5216002329/10000000000 : ℝ)*x 1 + (5437755343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925576357/10000000000 : ℝ)^4445 ≤ (588003586937/5000000000000 : ℝ)^3421 := by
    have hnat : (1925576357 : ℕ)^4445*5000000000000^3421 ≤ 588003586937^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925576357 10000000000 588003586937 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216002329/10000000000 : ℝ)^4445 ≤ (42926862622729/100000000000000 : ℝ)^3421 := by
    have hnat : (5216002329 : ℕ)^4445*100000000000000^3421 ≤ 42926862622729^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216002329 10000000000 42926862622729 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437755343/10000000000 : ℝ)^4445 ≤ (45313065623787/100000000000000 : ℝ)^3421 := by
    have hnat : (5437755343 : ℕ)^4445*100000000000000^3421 ≤ 45313065623787^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437755343 10000000000 45313065623787 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925576357/10000000000 : ℝ), (5216002329/10000000000 : ℝ), (5437755343/10000000000 : ℝ)] ![(588003586937/5000000000000 : ℝ), (42926862622729/100000000000000 : ℝ), (45313065623787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925576357/10000000000 : ℝ)|^4445 ≤ (588003586937/5000000000000 : ℝ)^3421
        have hw : |(-1925576357/10000000000 : ℝ)|=(1925576357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216002329/10000000000 : ℝ)|^4445 ≤ (42926862622729/100000000000000 : ℝ)^3421
        have hw : |(5216002329/10000000000 : ℝ)|=(5216002329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437755343/10000000000 : ℝ)|^4445 ≤ (45313065623787/100000000000000 : ℝ)^3421
        have hw : |(5437755343/10000000000 : ℝ)|=(5437755343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s4_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647669873/5000000000 : ℝ)*x 0 + (-1817504341/10000000000 : ℝ)*x 1 + (1087550931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647669873/5000000000 : ℝ)^4445 ≤ (43777162589669/100000000000000 : ℝ)^3421 := by
    have hnat : (2647669873 : ℕ)^4445*100000000000000^3421 ≤ 43777162589669^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647669873 5000000000 43777162589669 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1817504341/10000000000 : ℝ)^4445 ≤ (1363722402383/12500000000000 : ℝ)^3421 := by
    have hnat : (1817504341 : ℕ)^4445*12500000000000^3421 ≤ 1363722402383^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817504341 10000000000 1363722402383 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087550931/2000000000 : ℝ)^4445 ≤ (9062611634913/20000000000000 : ℝ)^3421 := by
    have hnat : (1087550931 : ℕ)^4445*20000000000000^3421 ≤ 9062611634913^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087550931 2000000000 9062611634913 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647669873/5000000000 : ℝ), (-1817504341/10000000000 : ℝ), (1087550931/2000000000 : ℝ)] ![(43777162589669/100000000000000 : ℝ), (1363722402383/12500000000000 : ℝ), (9062611634913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647669873/5000000000 : ℝ)|^4445 ≤ (43777162589669/100000000000000 : ℝ)^3421
        have hw : |(2647669873/5000000000 : ℝ)|=(2647669873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1817504341/10000000000 : ℝ)|^4445 ≤ (1363722402383/12500000000000 : ℝ)^3421
        have hw : |(-1817504341/10000000000 : ℝ)|=(1817504341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087550931/2000000000 : ℝ)|^4445 ≤ (9062611634913/20000000000000 : ℝ)^3421
        have hw : |(1087550931/2000000000 : ℝ)|=(1087550931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s4_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323834851/2500000000 : ℝ)*x 0 + (5437754827/10000000000 : ℝ)*x 1 + (-908752287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323834851/2500000000 : ℝ)^4445 ≤ (43777158916013/100000000000000 : ℝ)^3421 := by
    have hnat : (1323834851 : ℕ)^4445*100000000000000^3421 ≤ 43777158916013^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323834851 2500000000 43777158916013 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437754827/10000000000 : ℝ)^4445 ≤ (45313060036871/100000000000000 : ℝ)^3421 := by
    have hnat : (5437754827 : ℕ)^4445*100000000000000^3421 ≤ 45313060036871^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437754827 10000000000 45313060036871 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (908752287/5000000000 : ℝ)^4445 ≤ (2727445259079/25000000000000 : ℝ)^3421 := by
    have hnat : (908752287 : ℕ)^4445*25000000000000^3421 ≤ 2727445259079^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908752287 5000000000 2727445259079 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323834851/2500000000 : ℝ), (5437754827/10000000000 : ℝ), (-908752287/5000000000 : ℝ)] ![(43777158916013/100000000000000 : ℝ), (45313060036871/100000000000000 : ℝ), (2727445259079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323834851/2500000000 : ℝ)|^4445 ≤ (43777158916013/100000000000000 : ℝ)^3421
        have hw : |(1323834851/2500000000 : ℝ)|=(1323834851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437754827/10000000000 : ℝ)|^4445 ≤ (45313060036871/100000000000000 : ℝ)^3421
        have hw : |(5437754827/10000000000 : ℝ)|=(5437754827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-908752287/5000000000 : ℝ)|^4445 ≤ (2727445259079/25000000000000 : ℝ)^3421
        have hw : |(-908752287/5000000000 : ℝ)|=(908752287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s4_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287806977/10000000000 : ℝ)*x 0 + (4538698823/10000000000 : ℝ)*x 1 + (1012322943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287806977/10000000000 : ℝ)^4445 ≤ (8319420158213/25000000000000 : ℝ)^3421 := by
    have hnat : (4287806977 : ℕ)^4445*25000000000000^3421 ≤ 8319420158213^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287806977 10000000000 8319420158213 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538698823/10000000000 : ℝ)^4445 ≤ (35829555940403/100000000000000 : ℝ)^3421 := by
    have hnat : (4538698823 : ℕ)^4445*100000000000000^3421 ≤ 35829555940403^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538698823 10000000000 35829555940403 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012322943/2500000000 : ℝ)^4445 ≤ (30892763412509/100000000000000 : ℝ)^3421 := by
    have hnat : (1012322943 : ℕ)^4445*100000000000000^3421 ≤ 30892763412509^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012322943 2500000000 30892763412509 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287806977/10000000000 : ℝ), (4538698823/10000000000 : ℝ), (1012322943/2500000000 : ℝ)] ![(8319420158213/25000000000000 : ℝ), (35829555940403/100000000000000 : ℝ), (30892763412509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287806977/10000000000 : ℝ)|^4445 ≤ (8319420158213/25000000000000 : ℝ)^3421
        have hw : |(4287806977/10000000000 : ℝ)|=(4287806977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538698823/10000000000 : ℝ)|^4445 ≤ (35829555940403/100000000000000 : ℝ)^3421
        have hw : |(4538698823/10000000000 : ℝ)|=(4538698823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1012322943/2500000000 : ℝ)|^4445 ≤ (30892763412509/100000000000000 : ℝ)^3421
        have hw : |(1012322943/2500000000 : ℝ)|=(1012322943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10663/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10747/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10663/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10663/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10663/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10663/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10663/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10663/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10663/100000 : ℝ) ^ (4443/1024 : ℝ) ≤ (3027386504896527/50000000000000000000 : ℝ) := by
    have hpowers : (10663/100000 : ℝ)^4443 ≤ (3027386504896527/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10663 : ℕ)^4443*50000000000000000000^1024 ≤ 3027386504896527^1024*100000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10663 100000 3027386504896527 50000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10663/100000 : ℝ)) (X := (3027386504896527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15579/100000 : ℝ) ^ (4443/1024 : ℝ) ≤ (1568579269894191/5000000000000000000 : ℝ) := by
    have hpowers : (15579/100000 : ℝ)^4443 ≤ (1568579269894191/5000000000000000000 : ℝ)^1024 := by
      have hnat : (15579 : ℕ)^4443*5000000000000000000^1024 ≤ 1568579269894191^1024*100000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15579 100000 1568579269894191 5000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15579/100000 : ℝ)) (X := (1568579269894191/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003027386504896527/25000000000000000000 : ℝ) ≤ (2500069770410781/2500000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (25003027386504896527/25000000000000000000 : ℝ)^1024 ≤ (2500069770410781/2500000000000000 : ℝ)^4443 := by
      have hnat : (25003027386504896527 : ℕ)^1024*2500000000000000^4443 ≤ 2500069770410781^4443*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003027386504896527 25000000000000000000 2500069770410781 2500000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500069770410781/2500000000000000 : ℝ)) (X := (25003027386504896527/25000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018713179203838437/50000000000000000000 : ℝ) ≤ (5000431229725257/5000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (50018713179203838437/50000000000000000000 : ℝ)^1024 ≤ (5000431229725257/5000000000000000 : ℝ)^4443 := by
      have hnat : (50018713179203838437 : ℕ)^1024*5000000000000000^4443 ≤ 5000431229725257^4443*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018713179203838437 50000000000000000000 5000431229725257 5000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000431229725257/5000000000000000 : ℝ)) (X := (50018713179203838437/50000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501568579269894191/2500000000000000000 : ℝ) ≤ (625090364828619/625000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (2501568579269894191/2500000000000000000 : ℝ)^1024 ≤ (625090364828619/625000000000000 : ℝ)^4443 := by
      have hnat : (2501568579269894191 : ℕ)^1024*625000000000000^4443 ≤ 625090364828619^4443*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501568579269894191 2500000000000000000 625090364828619 625000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625090364828619/625000000000000 : ℝ)) (X := (2501568579269894191/2500000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3027386504896527/50000000000000000000 : ℝ) ≤ ((12287232712559299611/12290000000000000000 : ℝ)+2*(58337780739/49160000000000 : ℝ)*(10663/100000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (12287232712559299611/12290000000000000000 : ℝ)+2*(58337780739/49160000000000 : ℝ)*(10663/100000 : ℝ)=(2500069770410781/2500000000000000 : ℝ) by norm_num, show 1+2*(3027386504896527/50000000000000000000 : ℝ)=(25003027386504896527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1568579269894191/5000000000000000000 : ℝ)+(3027386504896527/50000000000000000000 : ℝ) ≤ ((12287232712559299611/12290000000000000000 : ℝ)+(58337780739/49160000000000 : ℝ)*((15579/100000 : ℝ)+(10663/100000 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (12287232712559299611/12290000000000000000 : ℝ)+(58337780739/49160000000000 : ℝ)*((15579/100000 : ℝ)+(10663/100000 : ℝ))=(5000431229725257/5000000000000000 : ℝ) by norm_num, show 1+(1568579269894191/5000000000000000000 : ℝ)+(3027386504896527/50000000000000000000 : ℝ)=(50018713179203838437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1568579269894191/5000000000000000000 : ℝ) ≤ ((12287232712559299611/12290000000000000000 : ℝ)+2*(58337780739/49160000000000 : ℝ)*(15579/100000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (12287232712559299611/12290000000000000000 : ℝ)+2*(58337780739/49160000000000 : ℝ)*(15579/100000 : ℝ)=(625090364828619/625000000000000 : ℝ) by norm_num, show 1+2*(1568579269894191/5000000000000000000 : ℝ)=(2501568579269894191/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12287232712559299611/12290000000000000000 : ℝ)*(X 1 0+X 2 0)+(58337780739/49160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10663/100000 : ℝ)) (hi := (15579/100000 : ℝ)) (c := (12287232712559299611/12290000000000000000 : ℝ)) (alpha := (58337780739/49160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12287232712559299611/12290000000000000000 : ℝ)*(X 0 1+X 2 1)+(58337780739/49160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10663/100000 : ℝ)) (hi := (15579/100000 : ℝ)) (c := (12287232712559299611/12290000000000000000 : ℝ)) (alpha := (58337780739/49160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12287232712559299611/12290000000000000000 : ℝ)*(X 0 2+X 1 2)+(58337780739/49160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10663/100000 : ℝ)) (hi := (15579/100000 : ℝ)) (c := (12287232712559299611/12290000000000000000 : ℝ)) (alpha := (58337780739/49160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-7702179/40000000 : ℝ)*X 0 0+(135972877/250000000 : ℝ)*X 0 1+(1303712857/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676898087/5000000000 : ℝ)*X 1 0+(-408081637/2000000000 : ℝ)*X 1 1+(5214851153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535379603/1000000000 : ℝ)*X 2 0+(5214851391/10000000000 : ℝ)*X 2 1+(-1020204031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071934289/2500000000 : ℝ)*X 0 0+(4046731707/10000000000 : ℝ)*X 0 1+(2270620563/5000000000 : ℝ)*X 0 2+(1071934289/2500000000 : ℝ)*X 1 0+(4046731707/10000000000 : ℝ)*X 1 1+(2270620563/5000000000 : ℝ)*X 1 2+(1071934289/2500000000 : ℝ)*X 2 0+(4046731707/10000000000 : ℝ)*X 2 1+(2270620563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1925576357/10000000000 : ℝ)*X 0 0+(5216002329/10000000000 : ℝ)*X 0 1+(5437755343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647669873/5000000000 : ℝ)*X 1 0+(-1817504341/10000000000 : ℝ)*X 1 1+(1087550931/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323834851/2500000000 : ℝ)*X 2 0+(5437754827/10000000000 : ℝ)*X 2 1+(-908752287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4287806977/10000000000 : ℝ)*X 0 0+(4538698823/10000000000 : ℝ)*X 0 1+(1012322943/2500000000 : ℝ)*X 0 2+(4287806977/10000000000 : ℝ)*X 1 0+(4538698823/10000000000 : ℝ)*X 1 1+(1012322943/2500000000 : ℝ)*X 1 2+(4287806977/10000000000 : ℝ)*X 2 0+(4538698823/10000000000 : ℝ)*X 2 1+(1012322943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1763352723965115093052979253/307250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (508453861/50000000000000 : ℝ)*(base19) + (54371067/6250000000000 : ℝ)*(base23) + (14417269/100000000000000 : ℝ)*(lower2) + (5920307/12500000000000 : ℝ)*(upper3) + (121203701/100000000000000 : ℝ)*(upper5) + (1621316266168741/50000000000000 : ℝ)*(major0) + (1621316266168741/50000000000000 : ℝ)*(major1) + (1621316266168741/50000000000000 : ℝ)*(major2) + (2231514929664867/50000000000000 : ℝ)*(sp0) + (1115760760445727/25000000000000 : ℝ)*(sp1) + (2231521594376779/50000000000000 : ℝ)*(sp2) + (2022213953509019/100000000000000 : ℝ)*(sp3) + (14199360897/100000000000000 : ℝ)*(sp4) + (6861170429/100000000000000 : ℝ)*(sp7) + (252777601834931/12500000000000 : ℝ)*(f.failure) + (446304405869063/10000000000000 : ℝ)*(f.sum) + (2211228491327/1229000000000000000000000000 : ℝ)*base65 + (2491410519427090249/614500000000000000000000000000000 : ℝ)*base68 + (3550022003671090249/614500000000000000000000000000000 : ℝ)*base70 + (676091945010909751/614500000000000000000000000000000 : ℝ)*base71 + (339972568519/1229000000000000000000000000 : ℝ)*base73 + (2099623860735590249/614500000000000000000000000000000 : ℝ)*base76 + (4068266675364909751/614500000000000000000000000000000 : ℝ)*base77 + (2174317055929590249/614500000000000000000000000000000 : ℝ)*base80 + (821722401561/245800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (879371/156250000000000000000 : ℝ)*base90 + (879371/156250000000000000000 : ℝ)*base92 + (879371/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (376174029534774335026562997/307250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49544937/3125000000000 : ℝ)*(base19) + (284996807/25000000000000 : ℝ)*(base23) + (414509/25000000000000 : ℝ)*(upper2) + (8919853/100000000000000 : ℝ)*(upper3) + (98006731/25000000000000 : ℝ)*(upper5) + (3276407000454509/100000000000000 : ℝ)*(major0) + (3276407000454509/100000000000000 : ℝ)*(major1) + (3276407000454509/100000000000000 : ℝ)*(major2) + (4532680869/25000000000000 : ℝ)*(sp1) + (1939239571/50000000000000 : ℝ)*(sp2) + (1127382546886063/25000000000000 : ℝ)*(sp4) + (563688808922849/12500000000000 : ℝ)*(sp5) + (4509525169077883/100000000000000 : ℝ)*(sp6) + (2043283772553909/100000000000000 : ℝ)*(sp7) + (2043283772553909/100000000000000 : ℝ)*(f.failure) + (1127382546886063/25000000000000 : ℝ)*(f.sum) + (4370660751069/2458000000000000000000000000 : ℝ)*base65 + (1104320199190354001/1229000000000000000000000000000000 : ℝ)*base68 + (1143934766108645999/1229000000000000000000000000000000 : ℝ)*base69 + (7748100919276354001/1229000000000000000000000000000000 : ℝ)*base72 + (2474990079601/2458000000000000000000000000 : ℝ)*base73 + (7048242674699354001/1229000000000000000000000000000000 : ℝ)*base76 + (4495400436220354001/1229000000000000000000000000000000 : ℝ)*base78 + (16863559655985354001/1229000000000000000000000000000000 : ℝ)*base80 + (705567410913/491600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4003931/1250000000000000000000 : ℝ)*base89 + (4003931/1250000000000000000000 : ℝ)*base91 + (4003931/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1474_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10663/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1474_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1474_s5_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925639009/10000000000 : ℝ)*x 0 + (1359575937/2500000000 : ℝ)*x 1 + (2607700267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925639009/10000000000 : ℝ)^4445 ≤ (2352113781761/20000000000000 : ℝ)^3421 := by
    have hnat : (1925639009 : ℕ)^4445*20000000000000^3421 ≤ 2352113781761^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925639009 10000000000 2352113781761 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359575937/2500000000 : ℝ)^4445 ≤ (2265950174517/5000000000000 : ℝ)^3421 := by
    have hnat : (1359575937 : ℕ)^4445*5000000000000^3421 ≤ 2265950174517^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359575937 2500000000 2265950174517 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607700267/5000000000 : ℝ)^4445 ≤ (4292042758439/10000000000000 : ℝ)^3421 := by
    have hnat : (2607700267 : ℕ)^4445*10000000000000^3421 ≤ 4292042758439^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607700267 5000000000 4292042758439 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925639009/10000000000 : ℝ), (1359575937/2500000000 : ℝ), (2607700267/5000000000 : ℝ)] ![(2352113781761/20000000000000 : ℝ), (2265950174517/5000000000000 : ℝ), (4292042758439/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925639009/10000000000 : ℝ)|^4445 ≤ (2352113781761/20000000000000 : ℝ)^3421
        have hw : |(-1925639009/10000000000 : ℝ)|=(1925639009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359575937/2500000000 : ℝ)|^4445 ≤ (2265950174517/5000000000000 : ℝ)^3421
        have hw : |(1359575937/2500000000 : ℝ)|=(1359575937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607700267/5000000000 : ℝ)|^4445 ≤ (4292042758439/10000000000000 : ℝ)^3421
        have hw : |(2607700267/5000000000 : ℝ)|=(2607700267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676818877/5000000000 : ℝ)*x 0 + (-203989281/1000000000 : ℝ)*x 1 + (1303849993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676818877/5000000000 : ℝ)^4445 ≤ (1110110267227/2500000000000 : ℝ)^3421 := by
    have hnat : (2676818877 : ℕ)^4445*2500000000000^3421 ≤ 1110110267227^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676818877 5000000000 1110110267227 2500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203989281/1000000000 : ℝ)^4445 ≤ (316879193071/2500000000000 : ℝ)^3421 := by
    have hnat : (203989281 : ℕ)^4445*2500000000000^3421 ≤ 316879193071^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203989281 1000000000 316879193071 2500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303849993/2500000000 : ℝ)^4445 ≤ (42920421574987/100000000000000 : ℝ)^3421 := by
    have hnat : (1303849993 : ℕ)^4445*100000000000000^3421 ≤ 42920421574987^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303849993 2500000000 42920421574987 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676818877/5000000000 : ℝ), (-203989281/1000000000 : ℝ), (1303849993/2500000000 : ℝ)] ![(1110110267227/2500000000000 : ℝ), (316879193071/2500000000000 : ℝ), (42920421574987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676818877/5000000000 : ℝ)|^4445 ≤ (1110110267227/2500000000000 : ℝ)^3421
        have hw : |(2676818877/5000000000 : ℝ)|=(2676818877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-203989281/1000000000 : ℝ)|^4445 ≤ (316879193071/2500000000000 : ℝ)^3421
        have hw : |(-203989281/1000000000 : ℝ)|=(203989281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303849993/2500000000 : ℝ)|^4445 ≤ (42920421574987/100000000000000 : ℝ)^3421
        have hw : |(1303849993/2500000000 : ℝ)|=(1303849993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353638899/10000000000 : ℝ)*x 0 + (5215398499/10000000000 : ℝ)*x 1 + (-2039893231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353638899/10000000000 : ℝ)^4445 ≤ (44404423028687/100000000000000 : ℝ)^3421 := by
    have hnat : (5353638899 : ℕ)^4445*100000000000000^3421 ≤ 44404423028687^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353638899 10000000000 44404423028687 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215398499/10000000000 : ℝ)^4445 ≤ (21460202912181/50000000000000 : ℝ)^3421 := by
    have hnat : (5215398499 : ℕ)^4445*50000000000000^3421 ≤ 21460202912181^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215398499 10000000000 21460202912181 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2039893231/10000000000 : ℝ)^4445 ≤ (792198195113/6250000000000 : ℝ)^3421 := by
    have hnat : (2039893231 : ℕ)^4445*6250000000000^3421 ≤ 792198195113^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039893231 10000000000 792198195113 6250000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353638899/10000000000 : ℝ), (5215398499/10000000000 : ℝ), (-2039893231/10000000000 : ℝ)] ![(44404423028687/100000000000000 : ℝ), (21460202912181/50000000000000 : ℝ), (792198195113/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353638899/10000000000 : ℝ)|^4445 ≤ (44404423028687/100000000000000 : ℝ)^3421
        have hw : |(5353638899/10000000000 : ℝ)|=(5353638899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215398499/10000000000 : ℝ)|^4445 ≤ (21460202912181/50000000000000 : ℝ)^3421
        have hw : |(5215398499/10000000000 : ℝ)|=(5215398499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2039893231/10000000000 : ℝ)|^4445 ≤ (792198195113/6250000000000 : ℝ)^3421
        have hw : |(-2039893231/10000000000 : ℝ)|=(2039893231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287794363/10000000000 : ℝ)*x 0 + (2024002889/5000000000 : ℝ)*x 1 + (567494241/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287794363/10000000000 : ℝ)^4445 ≤ (6655510686451/20000000000000 : ℝ)^3421 := by
    have hnat : (4287794363 : ℕ)^4445*20000000000000^3421 ≤ 6655510686451^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287794363 10000000000 6655510686451 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024002889/5000000000 : ℝ)^4445 ≤ (30880016216131/100000000000000 : ℝ)^3421 := by
    have hnat : (2024002889 : ℕ)^4445*100000000000000^3421 ≤ 30880016216131^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024002889 5000000000 30880016216131 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567494241/1250000000 : ℝ)^4445 ≤ (17921215167029/50000000000000 : ℝ)^3421 := by
    have hnat : (567494241 : ℕ)^4445*50000000000000^3421 ≤ 17921215167029^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567494241 1250000000 17921215167029 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287794363/10000000000 : ℝ), (2024002889/5000000000 : ℝ), (567494241/1250000000 : ℝ)] ![(6655510686451/20000000000000 : ℝ), (30880016216131/100000000000000 : ℝ), (17921215167029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287794363/10000000000 : ℝ)|^4445 ≤ (6655510686451/20000000000000 : ℝ)^3421
        have hw : |(4287794363/10000000000 : ℝ)|=(4287794363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2024002889/5000000000 : ℝ)|^4445 ≤ (30880016216131/100000000000000 : ℝ)^3421
        have hw : |(2024002889/5000000000 : ℝ)|=(2024002889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567494241/1250000000 : ℝ)|^4445 ≤ (17921215167029/50000000000000 : ℝ)^3421
        have hw : |(567494241/1250000000 : ℝ)|=(567494241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925669319/10000000000 : ℝ)*x 0 + (5216539931/10000000000 : ℝ)*x 1 + (679644531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925669319/10000000000 : ℝ)^4445 ≤ (5880404716593/50000000000000 : ℝ)^3421 := by
    have hnat : (1925669319 : ℕ)^4445*50000000000000^3421 ≤ 5880404716593^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925669319 10000000000 5880404716593 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216539931/10000000000 : ℝ)^4445 ≤ (1717304457141/4000000000000 : ℝ)^3421 := by
    have hnat : (5216539931 : ℕ)^4445*4000000000000^3421 ≤ 1717304457141^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216539931 10000000000 1717304457141 4000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679644531/1250000000 : ℝ)^4445 ≤ (45306579115069/100000000000000 : ℝ)^3421 := by
    have hnat : (679644531 : ℕ)^4445*100000000000000^3421 ≤ 45306579115069^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679644531 1250000000 45306579115069 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925669319/10000000000 : ℝ), (5216539931/10000000000 : ℝ), (679644531/1250000000 : ℝ)] ![(5880404716593/50000000000000 : ℝ), (1717304457141/4000000000000 : ℝ), (45306579115069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925669319/10000000000 : ℝ)|^4445 ≤ (5880404716593/50000000000000 : ℝ)^3421
        have hw : |(-1925669319/10000000000 : ℝ)|=(1925669319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216539931/10000000000 : ℝ)|^4445 ≤ (1717304457141/4000000000000 : ℝ)^3421
        have hw : |(5216539931/10000000000 : ℝ)|=(5216539931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679644531/1250000000 : ℝ)|^4445 ≤ (45306579115069/100000000000000 : ℝ)^3421
        have hw : |(679644531/1250000000 : ℝ)|=(679644531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661935449/1250000000 : ℝ)*x 0 + (-1818137043/10000000000 : ℝ)*x 1 + (5437156153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661935449/1250000000 : ℝ)^4445 ≤ (2188935387229/5000000000000 : ℝ)^3421 := by
    have hnat : (661935449 : ℕ)^4445*5000000000000^3421 ≤ 2188935387229^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661935449 1250000000 2188935387229 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1818137043/10000000000 : ℝ)^4445 ≤ (10914714149419/100000000000000 : ℝ)^3421 := by
    have hnat : (1818137043 : ℕ)^4445*100000000000000^3421 ≤ 10914714149419^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818137043 10000000000 10914714149419 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437156153/10000000000 : ℝ)^4445 ≤ (5663322260813/12500000000000 : ℝ)^3421 := by
    have hnat : (5437156153 : ℕ)^4445*12500000000000^3421 ≤ 5663322260813^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437156153 10000000000 5663322260813 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661935449/1250000000 : ℝ), (-1818137043/10000000000 : ℝ), (5437156153/10000000000 : ℝ)] ![(2188935387229/5000000000000 : ℝ), (10914714149419/100000000000000 : ℝ), (5663322260813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661935449/1250000000 : ℝ)|^4445 ≤ (2188935387229/5000000000000 : ℝ)^3421
        have hw : |(661935449/1250000000 : ℝ)|=(661935449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1818137043/10000000000 : ℝ)|^4445 ≤ (10914714149419/100000000000000 : ℝ)^3421
        have hw : |(-1818137043/10000000000 : ℝ)|=(1818137043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437156153/10000000000 : ℝ)|^4445 ≤ (5663322260813/12500000000000 : ℝ)^3421
        have hw : |(5437156153/10000000000 : ℝ)|=(5437156153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323870889/2500000000 : ℝ)*x 0 + (5437156149/10000000000 : ℝ)*x 1 + (-1818137099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323870889/2500000000 : ℝ)^4445 ≤ (10944676839469/25000000000000 : ℝ)^3421 := by
    have hnat : (1323870889 : ℕ)^4445*25000000000000^3421 ≤ 10944676839469^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323870889 2500000000 10944676839469 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437156149/10000000000 : ℝ)^4445 ≤ (11326644510799/25000000000000 : ℝ)^3421 := by
    have hnat : (5437156149 : ℕ)^4445*25000000000000^3421 ≤ 11326644510799^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437156149 10000000000 11326644510799 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1818137099/10000000000 : ℝ)^4445 ≤ (2728678646557/25000000000000 : ℝ)^3421 := by
    have hnat : (1818137099 : ℕ)^4445*25000000000000^3421 ≤ 2728678646557^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818137099 10000000000 2728678646557 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323870889/2500000000 : ℝ), (5437156149/10000000000 : ℝ), (-1818137099/10000000000 : ℝ)] ![(10944676839469/25000000000000 : ℝ), (11326644510799/25000000000000 : ℝ), (2728678646557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323870889/2500000000 : ℝ)|^4445 ≤ (10944676839469/25000000000000 : ℝ)^3421
        have hw : |(1323870889/2500000000 : ℝ)|=(1323870889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437156149/10000000000 : ℝ)|^4445 ≤ (11326644510799/25000000000000 : ℝ)^3421
        have hw : |(5437156149/10000000000 : ℝ)|=(5437156149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1818137099/10000000000 : ℝ)|^4445 ≤ (2728678646557/25000000000000 : ℝ)^3421
        have hw : |(-1818137099/10000000000 : ℝ)|=(1818137099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857572573/2000000000 : ℝ)*x 0 + (1134359703/2500000000 : ℝ)*x 1 + (2025269297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857572573/2000000000 : ℝ)^4445 ≤ (6655648842663/20000000000000 : ℝ)^3421 := by
    have hnat : (857572573 : ℕ)^4445*20000000000000^3421 ≤ 6655648842663^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857572573 2000000000 6655648842663 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134359703/2500000000 : ℝ)^4445 ≤ (35816632294733/100000000000000 : ℝ)^3421 := by
    have hnat : (1134359703 : ℕ)^4445*100000000000000^3421 ≤ 35816632294733^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134359703 2500000000 35816632294733 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025269297/5000000000 : ℝ)^4445 ≤ (30905123480139/100000000000000 : ℝ)^3421 := by
    have hnat : (2025269297 : ℕ)^4445*100000000000000^3421 ≤ 30905123480139^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025269297 5000000000 30905123480139 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857572573/2000000000 : ℝ), (1134359703/2500000000 : ℝ), (2025269297/5000000000 : ℝ)] ![(6655648842663/20000000000000 : ℝ), (35816632294733/100000000000000 : ℝ), (30905123480139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857572573/2000000000 : ℝ)|^4445 ≤ (6655648842663/20000000000000 : ℝ)^3421
        have hw : |(857572573/2000000000 : ℝ)|=(857572573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134359703/2500000000 : ℝ)|^4445 ≤ (35816632294733/100000000000000 : ℝ)^3421
        have hw : |(1134359703/2500000000 : ℝ)|=(1134359703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025269297/5000000000 : ℝ)|^4445 ≤ (30905123480139/100000000000000 : ℝ)^3421
        have hw : |(2025269297/5000000000 : ℝ)|=(2025269297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_8 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3459587/2000000000 : ℝ)*x 0 + (5864396173/10000000000 : ℝ)*x 1 + (5864643881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3459587/2000000000 : ℝ)^4445 ≤ (2577801579/10000000000000 : ℝ)^3421 := by
    have hnat : (3459587 : ℕ)^4445*10000000000000^3421 ≤ 2577801579^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3459587 2000000000 2577801579 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5864396173/10000000000 : ℝ)^4445 ≤ (49985739301673/100000000000000 : ℝ)^3421 := by
    have hnat : (5864396173 : ℕ)^4445*100000000000000^3421 ≤ 49985739301673^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5864396173 10000000000 49985739301673 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5864643881/10000000000 : ℝ)^4445 ≤ (3124280166941/6250000000000 : ℝ)^3421 := by
    have hnat : (5864643881 : ℕ)^4445*6250000000000^3421 ≤ 3124280166941^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5864643881 10000000000 3124280166941 6250000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3459587/2000000000 : ℝ), (5864396173/10000000000 : ℝ), (5864643881/10000000000 : ℝ)] ![(2577801579/10000000000000 : ℝ), (49985739301673/100000000000000 : ℝ), (3124280166941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3459587/2000000000 : ℝ)|^4445 ≤ (2577801579/10000000000000 : ℝ)^3421
        have hw : |(-3459587/2000000000 : ℝ)|=(3459587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5864396173/10000000000 : ℝ)|^4445 ≤ (49985739301673/100000000000000 : ℝ)^3421
        have hw : |(5864396173/10000000000 : ℝ)|=(5864396173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5864643881/10000000000 : ℝ)|^4445 ≤ (3124280166941/6250000000000 : ℝ)^3421
        have hw : |(5864643881/10000000000 : ℝ)|=(5864643881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s5_9 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1453423961/10000000000 : ℝ)*x 0 + (549254507/1000000000 : ℝ)*x 1 + (2747467103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1453423961/10000000000 : ℝ)^4445 ≤ (1631936082051/20000000000000 : ℝ)^3421 := by
    have hnat : (1453423961 : ℕ)^4445*20000000000000^3421 ≤ 1631936082051^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1453423961 10000000000 1631936082051 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549254507/1000000000 : ℝ)^4445 ≤ (4590718606081/10000000000000 : ℝ)^3421 := by
    have hnat : (549254507 : ℕ)^4445*10000000000000^3421 ≤ 4590718606081^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549254507 1000000000 4590718606081 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747467103/5000000000 : ℝ)^4445 ≤ (9186626704461/20000000000000 : ℝ)^3421 := by
    have hnat : (2747467103 : ℕ)^4445*20000000000000^3421 ≤ 9186626704461^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747467103 5000000000 9186626704461 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1453423961/10000000000 : ℝ), (549254507/1000000000 : ℝ), (2747467103/5000000000 : ℝ)] ![(1631936082051/20000000000000 : ℝ), (4590718606081/10000000000000 : ℝ), (9186626704461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1453423961/10000000000 : ℝ)|^4445 ≤ (1631936082051/20000000000000 : ℝ)^3421
        have hw : |(1453423961/10000000000 : ℝ)|=(1453423961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549254507/1000000000 : ℝ)|^4445 ≤ (4590718606081/10000000000000 : ℝ)^3421
        have hw : |(549254507/1000000000 : ℝ)|=(549254507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747467103/5000000000 : ℝ)|^4445 ≤ (9186626704461/20000000000000 : ℝ)^3421
        have hw : |(2747467103/5000000000 : ℝ)|=(2747467103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10759/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10747/100000 : ℝ) ^ (4443/1024 : ℝ) ≤ (1252893123741111/20000000000000000000 : ℝ) := by
    have hpowers : (10747/100000 : ℝ)^4443 ≤ (1252893123741111/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10747 : ℕ)^4443*20000000000000000000^1024 ≤ 1252893123741111^1024*100000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10747 100000 1252893123741111 20000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10747/100000 : ℝ)) (X := (1252893123741111/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4443/1024 : ℝ) ≤ (6116843293480153/20000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4443 ≤ (6116843293480153/20000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4443*20000000000000000000^1024 ≤ 6116843293480153^1024*3125^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 6116843293480153 20000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (6116843293480153/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001252893123741111/10000000000000000000 : ℝ) ≤ (2500072186625927/2500000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (10001252893123741111/10000000000000000000 : ℝ)^1024 ≤ (2500072186625927/2500000000000000 : ℝ)^4443 := by
      have hnat : (10001252893123741111 : ℕ)^1024*2500000000000000^4443 ≤ 2500072186625927^4443*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001252893123741111 10000000000000000000 2500072186625927 2500000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500072186625927/2500000000000000 : ℝ)) (X := (10001252893123741111/10000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250460608526076329/1250000000000000000 : ℝ) ≤ (400033965970587/400000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (1250460608526076329/1250000000000000000 : ℝ)^1024 ≤ (400033965970587/400000000000000 : ℝ)^4443 := by
      have hnat : (1250460608526076329 : ℕ)^1024*400000000000000^4443 ≤ 400033965970587^4443*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250460608526076329 1250000000000000000 400033965970587 400000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400033965970587/400000000000000 : ℝ)) (X := (1250460608526076329/1250000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006116843293480153/10000000000000000000 : ℝ) ≤ (5000704776012821/5000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (10006116843293480153/10000000000000000000 : ℝ)^1024 ≤ (5000704776012821/5000000000000000 : ℝ)^4443 := by
      have hnat : (10006116843293480153 : ℕ)^1024*5000000000000000^4443 ≤ 5000704776012821^4443*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006116843293480153 10000000000000000000 5000704776012821 5000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000704776012821/5000000000000000 : ℝ)) (X := (10006116843293480153/10000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1252893123741111/20000000000000000000 : ℝ) ≤ ((430902942274816863/431000000000000000 : ℝ)+2*(560402760967/474100000000000 : ℝ)*(10747/100000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (430902942274816863/431000000000000000 : ℝ)+2*(560402760967/474100000000000 : ℝ)*(10747/100000 : ℝ)=(2500072186625927/2500000000000000 : ℝ) by norm_num, show 1+2*(1252893123741111/20000000000000000000 : ℝ)=(10001252893123741111/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6116843293480153/20000000000000000000 : ℝ)+(1252893123741111/20000000000000000000 : ℝ) ≤ ((430902942274816863/431000000000000000 : ℝ)+(560402760967/474100000000000 : ℝ)*((484/3125 : ℝ)+(10747/100000 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (430902942274816863/431000000000000000 : ℝ)+(560402760967/474100000000000 : ℝ)*((484/3125 : ℝ)+(10747/100000 : ℝ))=(400033965970587/400000000000000 : ℝ) by norm_num, show 1+(6116843293480153/20000000000000000000 : ℝ)+(1252893123741111/20000000000000000000 : ℝ)=(1250460608526076329/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6116843293480153/20000000000000000000 : ℝ) ≤ ((430902942274816863/431000000000000000 : ℝ)+2*(560402760967/474100000000000 : ℝ)*(484/3125 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (430902942274816863/431000000000000000 : ℝ)+2*(560402760967/474100000000000 : ℝ)*(484/3125 : ℝ)=(5000704776012821/5000000000000000 : ℝ) by norm_num, show 1+2*(6116843293480153/20000000000000000000 : ℝ)=(10006116843293480153/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (430902942274816863/431000000000000000 : ℝ)*(X 1 0+X 2 0)+(560402760967/474100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (430902942274816863/431000000000000000 : ℝ)) (alpha := (560402760967/474100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (430902942274816863/431000000000000000 : ℝ)*(X 0 1+X 2 1)+(560402760967/474100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (430902942274816863/431000000000000000 : ℝ)) (alpha := (560402760967/474100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (430902942274816863/431000000000000000 : ℝ)*(X 0 2+X 1 2)+(560402760967/474100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (430902942274816863/431000000000000000 : ℝ)) (alpha := (560402760967/474100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1925639009/10000000000 : ℝ)*X 0 0+(1359575937/2500000000 : ℝ)*X 0 1+(2607700267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676818877/5000000000 : ℝ)*X 1 0+(-203989281/1000000000 : ℝ)*X 1 1+(1303849993/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353638899/10000000000 : ℝ)*X 2 0+(5215398499/10000000000 : ℝ)*X 2 1+(-2039893231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4287794363/10000000000 : ℝ)*X 0 0+(2024002889/5000000000 : ℝ)*X 0 1+(567494241/1250000000 : ℝ)*X 0 2+(4287794363/10000000000 : ℝ)*X 1 0+(2024002889/5000000000 : ℝ)*X 1 1+(567494241/1250000000 : ℝ)*X 1 2+(4287794363/10000000000 : ℝ)*X 2 0+(2024002889/5000000000 : ℝ)*X 2 1+(567494241/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1925669319/10000000000 : ℝ)*X 0 0+(5216539931/10000000000 : ℝ)*X 0 1+(679644531/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661935449/1250000000 : ℝ)*X 1 0+(-1818137043/10000000000 : ℝ)*X 1 1+(5437156153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323870889/2500000000 : ℝ)*X 2 0+(5437156149/10000000000 : ℝ)*X 2 1+(-1818137099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((857572573/2000000000 : ℝ)*X 0 0+(1134359703/2500000000 : ℝ)*X 0 1+(2025269297/5000000000 : ℝ)*X 0 2+(857572573/2000000000 : ℝ)*X 1 0+(1134359703/2500000000 : ℝ)*X 1 1+(2025269297/5000000000 : ℝ)*X 1 2+(857572573/2000000000 : ℝ)*X 2 0+(1134359703/2500000000 : ℝ)*X 2 1+(2025269297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-3459587/2000000000 : ℝ)*X 0 0+(5864396173/10000000000 : ℝ)*X 0 1+(5864643881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1453423961/10000000000 : ℝ)*X 0 0+(549254507/1000000000 : ℝ)*X 0 1+(2747467103/5000000000 : ℝ)*X 0 2+(1453423961/10000000000 : ℝ)*X 1 0+(549254507/1000000000 : ℝ)*X 1 1+(2747467103/5000000000 : ℝ)*X 1 2+(1453423961/10000000000 : ℝ)*X 2 0+(549254507/1000000000 : ℝ)*X 2 1+(2747467103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s5_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15776186555025877150070163/5387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395567973/100000000000000 : ℝ)*(lower2) + (87357941/20000000000000 : ℝ)*(lower3) + (41498523/12500000000000 : ℝ)*(lower5) + (814871898538633/25000000000000 : ℝ)*(major0) + (814871898538633/25000000000000 : ℝ)*(major1) + (814871898538633/25000000000000 : ℝ)*(major2) + (4486237908622657/100000000000000 : ℝ)*(sp0) + (44862366893617/1000000000000 : ℝ)*(sp1) + (2243108190316849/50000000000000 : ℝ)*(sp2) + (1016365679038949/50000000000000 : ℝ)*(sp3) + (6171473289/100000000000000 : ℝ)*(sp5) + (6620050323/25000000000000 : ℝ)*(sp6) + (1238053083/25000000000000 : ℝ)*(sp8) + (871786353/100000000000000 : ℝ)*(sp9) + (2032732229864251/100000000000000 : ℝ)*(f.failure) + (1121560715208747/25000000000000 : ℝ)*(f.sum) + (50750536660363/11852500000000000000000000000 : ℝ)*base66 + (32759952646488931/118525000000000000000000000000000 : ℝ)*base68 + (620399893553361069/118525000000000000000000000000000 : ℝ)*base69 + (809177540855286069/118525000000000000000000000000000 : ℝ)*base71 + (204131184632091/23705000000000000000000000000 : ℝ)*base74 + (568186041286686069/118525000000000000000000000000000 : ℝ)*base75 + (1512914119039863931/118525000000000000000000000000000 : ℝ)*base78 + (200907351202061069/118525000000000000000000000000000 : ℝ)*base79 + (2710882451479/1481562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (240491/1250000000000000000000 : ℝ)*base90 + (240491/1250000000000000000000 : ℝ)*base92 + (240491/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (918083113656783728856505827/59262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (334255779/100000000000000 : ℝ)*(lower3) + (3996467/12500000000000 : ℝ)*(lower4) + (46963173/20000000000000 : ℝ)*(lower5) + (823321611784587/25000000000000 : ℝ)*(major0) + (823321611784587/25000000000000 : ℝ)*(major1) + (823321611784587/25000000000000 : ℝ)*(major2) + (5792805529/100000000000000 : ℝ)*(sp1) + (3100967109/100000000000000 : ℝ)*(sp2) + (4532758176087057/100000000000000 : ℝ)*(sp4) + (283297261879371/6250000000000 : ℝ)*(sp5) + (906551776381671/20000000000000 : ℝ)*(sp6) + (1026903786923223/50000000000000 : ℝ)*(sp7) + (3806788409/100000000000000 : ℝ)*(sp8) + (176322579/6250000000000 : ℝ)*(sp9) + (205381039500771/10000000000000 : ℝ)*(f.failure) + (906552396575093/20000000000000 : ℝ)*(f.sum) + (29734198138209/5926250000000000000000000000 : ℝ)*base65 + (56510646099113609/118525000000000000000000000000000 : ℝ)*base68 + (261725622628461391/118525000000000000000000000000000 : ℝ)*base69 + (1659187208095513609/118525000000000000000000000000000 : ℝ)*base72 + (78829336525123/11852500000000000000000000000 : ℝ)*base73 + (438600014206686391/118525000000000000000000000000000 : ℝ)*base75 + (947337385549161391/118525000000000000000000000000000 : ℝ)*base77 + (697715788092336391/118525000000000000000000000000000 : ℝ)*base79 + (11721378520449/5926250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (761811/125000000000000000000 : ℝ)*base90 + (761811/125000000000000000000 : ℝ)*base92 + (761811/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1474_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1474_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1474_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1474_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1474_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1474_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
