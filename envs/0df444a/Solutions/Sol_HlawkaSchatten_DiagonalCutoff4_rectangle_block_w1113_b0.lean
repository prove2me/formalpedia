-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1113_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:50.120812+00:00
-- url     : https://prove2.me/submissions/d5f78dd4-4948-4348-bfba-d2ed7dccec0b

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
theorem support_rectangle_w1113_s0_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-950511603/5000000000 : ℝ)*x 0 + (757632147/1250000000 : ℝ)*x 1 + (4776793653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (950511603/5000000000 : ℝ)^4153 ≤ (1104149915707/10000000000000 : ℝ)^3129 := by
    have hnat : (950511603 : ℕ)^4153*10000000000000^3129 ≤ 1104149915707^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950511603 5000000000 1104149915707 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757632147/1250000000 : ℝ)^4153 ≤ (51449946031723/100000000000000 : ℝ)^3129 := by
    have hnat : (757632147 : ℕ)^4153*100000000000000^3129 ≤ 51449946031723^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757632147 1250000000 51449946031723 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4776793653/10000000000 : ℝ)^4153 ≤ (37508554797031/100000000000000 : ℝ)^3129 := by
    have hnat : (4776793653 : ℕ)^4153*100000000000000^3129 ≤ 37508554797031^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776793653 10000000000 37508554797031 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-950511603/5000000000 : ℝ), (757632147/1250000000 : ℝ), (4776793653/10000000000 : ℝ)] ![(1104149915707/10000000000000 : ℝ), (51449946031723/100000000000000 : ℝ), (37508554797031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-950511603/5000000000 : ℝ)|^4153 ≤ (1104149915707/10000000000000 : ℝ)^3129
        have hw : |(-950511603/5000000000 : ℝ)|=(950511603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(757632147/1250000000 : ℝ)|^4153 ≤ (51449946031723/100000000000000 : ℝ)^3129
        have hw : |(757632147/1250000000 : ℝ)|=(757632147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4776793653/10000000000 : ℝ)|^4153 ≤ (37508554797031/100000000000000 : ℝ)^3129
        have hw : |(4776793653/10000000000 : ℝ)|=(4776793653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s0_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5518427019/10000000000 : ℝ)*x 0 + (-1319439001/5000000000 : ℝ)*x 1 + (955358743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518427019/10000000000 : ℝ)^4153 ≤ (45427777928367/100000000000000 : ℝ)^3129 := by
    have hnat : (5518427019 : ℕ)^4153*100000000000000^3129 ≤ 45427777928367^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518427019 10000000000 45427777928367 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319439001/5000000000 : ℝ)^4153 ≤ (17063666612323/100000000000000 : ℝ)^3129 := by
    have hnat : (1319439001 : ℕ)^4153*100000000000000^3129 ≤ 17063666612323^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319439001 5000000000 17063666612323 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955358743/2000000000 : ℝ)^4153 ≤ (18754277721597/50000000000000 : ℝ)^3129 := by
    have hnat : (955358743 : ℕ)^4153*50000000000000^3129 ≤ 18754277721597^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955358743 2000000000 18754277721597 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518427019/10000000000 : ℝ), (-1319439001/5000000000 : ℝ), (955358743/2000000000 : ℝ)] ![(45427777928367/100000000000000 : ℝ), (17063666612323/100000000000000 : ℝ), (18754277721597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518427019/10000000000 : ℝ)|^4153 ≤ (45427777928367/100000000000000 : ℝ)^3129
        have hw : |(5518427019/10000000000 : ℝ)|=(5518427019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1319439001/5000000000 : ℝ)|^4153 ≤ (17063666612323/100000000000000 : ℝ)^3129
        have hw : |(-1319439001/5000000000 : ℝ)|=(1319439001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955358743/2000000000 : ℝ)|^4153 ≤ (18754277721597/50000000000000 : ℝ)^3129
        have hw : |(955358743/2000000000 : ℝ)|=(955358743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s0_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5518427197/10000000000 : ℝ)*x 0 + (597099193/1250000000 : ℝ)*x 1 + (-2638877983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518427197/10000000000 : ℝ)^4153 ≤ (45427779873201/100000000000000 : ℝ)^3129 := by
    have hnat : (5518427197 : ℕ)^4153*100000000000000^3129 ≤ 45427779873201^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518427197 10000000000 45427779873201 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597099193/1250000000 : ℝ)^4153 ≤ (7501710732207/20000000000000 : ℝ)^3129 := by
    have hnat : (597099193 : ℕ)^4153*20000000000000^3129 ≤ 7501710732207^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597099193 1250000000 7501710732207 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2638877983/10000000000 : ℝ)^4153 ≤ (17063666449257/100000000000000 : ℝ)^3129 := by
    have hnat : (2638877983 : ℕ)^4153*100000000000000^3129 ≤ 17063666449257^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638877983 10000000000 17063666449257 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518427197/10000000000 : ℝ), (597099193/1250000000 : ℝ), (-2638877983/10000000000 : ℝ)] ![(45427779873201/100000000000000 : ℝ), (7501710732207/20000000000000 : ℝ), (17063666449257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518427197/10000000000 : ℝ)|^4153 ≤ (45427779873201/100000000000000 : ℝ)^3129
        have hw : |(5518427197/10000000000 : ℝ)|=(5518427197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597099193/1250000000 : ℝ)|^4153 ≤ (7501710732207/20000000000000 : ℝ)^3129
        have hw : |(597099193/1250000000 : ℝ)|=(597099193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2638877983/10000000000 : ℝ)|^4153 ≤ (17063666449257/100000000000000 : ℝ)^3129
        have hw : |(-2638877983/10000000000 : ℝ)|=(2638877983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s0_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203346651/10000000000 : ℝ)*x 0 + (1561230131/5000000000 : ℝ)*x 1 + (5662944357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203346651/10000000000 : ℝ)^4153 ≤ (31652831026423/100000000000000 : ℝ)^3129 := by
    have hnat : (4203346651 : ℕ)^4153*100000000000000^3129 ≤ 31652831026423^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203346651 10000000000 31652831026423 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561230131/5000000000 : ℝ)^4153 ≤ (21333662640617/100000000000000 : ℝ)^3129 := by
    have hnat : (1561230131 : ℕ)^4153*100000000000000^3129 ≤ 21333662640617^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561230131 5000000000 21333662640617 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662944357/10000000000 : ℝ)^4153 ≤ (4701350631527/10000000000000 : ℝ)^3129 := by
    have hnat : (5662944357 : ℕ)^4153*10000000000000^3129 ≤ 4701350631527^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662944357 10000000000 4701350631527 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203346651/10000000000 : ℝ), (1561230131/5000000000 : ℝ), (5662944357/10000000000 : ℝ)] ![(31652831026423/100000000000000 : ℝ), (21333662640617/100000000000000 : ℝ), (4701350631527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203346651/10000000000 : ℝ)|^4153 ≤ (31652831026423/100000000000000 : ℝ)^3129
        have hw : |(4203346651/10000000000 : ℝ)|=(4203346651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561230131/5000000000 : ℝ)|^4153 ≤ (21333662640617/100000000000000 : ℝ)^3129
        have hw : |(1561230131/5000000000 : ℝ)|=(1561230131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662944357/10000000000 : ℝ)|^4153 ≤ (4701350631527/10000000000000 : ℝ)^3129
        have hw : |(5662944357/10000000000 : ℝ)|=(5662944357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s0_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-76250233/400000000 : ℝ)*x 0 + (300621123/625000000 : ℝ)*x 1 + (602674907/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76250233/400000000 : ℝ)^4153 ≤ (5540927738099/50000000000000 : ℝ)^3129 := by
    have hnat : (76250233 : ℕ)^4153*50000000000000^3129 ≤ 5540927738099^3129*400000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76250233 400000000 5540927738099 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300621123/625000000 : ℝ)^4153 ≤ (37854375752477/100000000000000 : ℝ)^3129 := by
    have hnat : (300621123 : ℕ)^4153*100000000000000^3129 ≤ 37854375752477^3129*625000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300621123 625000000 37854375752477 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602674907/1000000000 : ℝ)^4153 ≤ (12765942191281/25000000000000 : ℝ)^3129 := by
    have hnat : (602674907 : ℕ)^4153*25000000000000^3129 ≤ 12765942191281^3129*1000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602674907 1000000000 12765942191281 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76250233/400000000 : ℝ), (300621123/625000000 : ℝ), (602674907/1000000000 : ℝ)] ![(5540927738099/50000000000000 : ℝ), (37854375752477/100000000000000 : ℝ), (12765942191281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76250233/400000000 : ℝ)|^4153 ≤ (5540927738099/50000000000000 : ℝ)^3129
        have hw : |(-76250233/400000000 : ℝ)|=(76250233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300621123/625000000 : ℝ)|^4153 ≤ (37854375752477/100000000000000 : ℝ)^3129
        have hw : |(300621123/625000000 : ℝ)|=(300621123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(602674907/1000000000 : ℝ)|^4153 ≤ (12765942191281/25000000000000 : ℝ)^3129
        have hw : |(602674907/1000000000 : ℝ)|=(602674907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s0_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646200937/1250000000 : ℝ)*x 0 + (-1388923433/10000000000 : ℝ)*x 1 + (753343941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646200937/1250000000 : ℝ)^4153 ≤ (20828278801177/50000000000000 : ℝ)^3129 := by
    have hnat : (646200937 : ℕ)^4153*50000000000000^3129 ≤ 20828278801177^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646200937 1250000000 20828278801177 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388923433/10000000000 : ℝ)^4153 ≤ (113744468379/1562500000000 : ℝ)^3129 := by
    have hnat : (1388923433 : ℕ)^4153*1562500000000^3129 ≤ 113744468379^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388923433 10000000000 113744468379 1562500000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753343941/1250000000 : ℝ)^4153 ≤ (51063796407033/100000000000000 : ℝ)^3129 := by
    have hnat : (753343941 : ℕ)^4153*100000000000000^3129 ≤ 51063796407033^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753343941 1250000000 51063796407033 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646200937/1250000000 : ℝ), (-1388923433/10000000000 : ℝ), (753343941/1250000000 : ℝ)] ![(20828278801177/50000000000000 : ℝ), (113744468379/1562500000000 : ℝ), (51063796407033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646200937/1250000000 : ℝ)|^4153 ≤ (20828278801177/50000000000000 : ℝ)^3129
        have hw : |(646200937/1250000000 : ℝ)|=(646200937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1388923433/10000000000 : ℝ)|^4153 ≤ (113744468379/1562500000000 : ℝ)^3129
        have hw : |(-1388923433/10000000000 : ℝ)|=(1388923433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753343941/1250000000 : ℝ)|^4153 ≤ (51063796407033/100000000000000 : ℝ)^3129
        have hw : |(753343941/1250000000 : ℝ)|=(753343941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s0_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1033922133/2000000000 : ℝ)*x 0 + (1506687391/2500000000 : ℝ)*x 1 + (-1388921737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033922133/2000000000 : ℝ)^4153 ≤ (41656591494921/100000000000000 : ℝ)^3129 := by
    have hnat : (1033922133 : ℕ)^4153*100000000000000^3129 ≤ 41656591494921^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033922133 2000000000 41656591494921 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506687391/2500000000 : ℝ)^4153 ≤ (10212754864099/20000000000000 : ℝ)^3129 := by
    have hnat : (1506687391 : ℕ)^4153*20000000000000^3129 ≤ 10212754864099^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506687391 2500000000 10212754864099 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1388921737/10000000000 : ℝ)^4153 ≤ (7279634178101/100000000000000 : ℝ)^3129 := by
    have hnat : (1388921737 : ℕ)^4153*100000000000000^3129 ≤ 7279634178101^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388921737 10000000000 7279634178101 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033922133/2000000000 : ℝ), (1506687391/2500000000 : ℝ), (-1388921737/10000000000 : ℝ)] ![(41656591494921/100000000000000 : ℝ), (10212754864099/20000000000000 : ℝ), (7279634178101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033922133/2000000000 : ℝ)|^4153 ≤ (41656591494921/100000000000000 : ℝ)^3129
        have hw : |(1033922133/2000000000 : ℝ)|=(1033922133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506687391/2500000000 : ℝ)|^4153 ≤ (10212754864099/20000000000000 : ℝ)^3129
        have hw : |(1506687391/2500000000 : ℝ)|=(1506687391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1388921737/10000000000 : ℝ)|^4153 ≤ (7279634178101/100000000000000 : ℝ)^3129
        have hw : |(-1388921737/10000000000 : ℝ)|=(1388921737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s0_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4213694177/10000000000 : ℝ)*x 0 + (5597382219/10000000000 : ℝ)*x 1 + (79758099/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213694177/10000000000 : ℝ)^4153 ≤ (396953675293/1250000000000 : ℝ)^3129 := by
    have hnat : (4213694177 : ℕ)^4153*1250000000000^3129 ≤ 396953675293^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213694177 10000000000 396953675293 1250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5597382219/10000000000 : ℝ)^4153 ≤ (23146229172351/50000000000000 : ℝ)^3129 := by
    have hnat : (5597382219 : ℕ)^4153*50000000000000^3129 ≤ 23146229172351^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597382219 10000000000 23146229172351 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79758099/250000000 : ℝ)^4153 ≤ (5487811904689/25000000000000 : ℝ)^3129 := by
    have hnat : (79758099 : ℕ)^4153*25000000000000^3129 ≤ 5487811904689^3129*250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79758099 250000000 5487811904689 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213694177/10000000000 : ℝ), (5597382219/10000000000 : ℝ), (79758099/250000000 : ℝ)] ![(396953675293/1250000000000 : ℝ), (23146229172351/50000000000000 : ℝ), (5487811904689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213694177/10000000000 : ℝ)|^4153 ≤ (396953675293/1250000000000 : ℝ)^3129
        have hw : |(4213694177/10000000000 : ℝ)|=(4213694177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5597382219/10000000000 : ℝ)|^4153 ≤ (23146229172351/50000000000000 : ℝ)^3129
        have hw : |(5597382219/10000000000 : ℝ)|=(5597382219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79758099/250000000 : ℝ)|^4153 ≤ (5487811904689/25000000000000 : ℝ)^3129
        have hw : |(79758099/250000000 : ℝ)|=(79758099/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (147/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27927/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8305/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8305 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8305*1^2048 ≤ 0^2048*1^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8305/2048 : ℝ) ≤ (1216895594328147163/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8305 ≤ (1216895594328147163/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8305*50000000000000000000^2048 ≤ 1216895594328147163^2048*5^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1216895594328147163 50000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1216895594328147163/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8305 := by
      have hnat : (1 : ℕ)^2048*1^8305 ≤ 1^8305*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51216895594328147163/50000000000000000000 : ℝ) ≤ (2514868591585099/2500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (51216895594328147163/50000000000000000000 : ℝ)^2048 ≤ (2514868591585099/2500000000000000 : ℝ)^8305 := by
      have hnat : (51216895594328147163 : ℕ)^2048*2500000000000000^8305 ≤ 2514868591585099^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51216895594328147163 50000000000000000000 2514868591585099 2500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514868591585099/2500000000000000 : ℝ)) (X := (51216895594328147163/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26216895594328147163/25000000000000000000 : ℝ) ≤ (1264868591585099/1250000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (26216895594328147163/25000000000000000000 : ℝ)^2048 ≤ (1264868591585099/1250000000000000 : ℝ)^8305 := by
      have hnat : (26216895594328147163 : ℕ)^2048*1250000000000000^8305 ≤ 1264868591585099^8305*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26216895594328147163 25000000000000000000 1264868591585099 1250000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264868591585099/1250000000000000 : ℝ)) (X := (26216895594328147163/25000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14868591585099/1000000000000000 : ℝ)*(0 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14868591585099/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1216895594328147163/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14868591585099/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (1 : ℝ)+(14868591585099/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514868591585099/2500000000000000 : ℝ) by norm_num, show 1+(1216895594328147163/50000000000000000000 : ℝ)+(0 : ℝ)=(51216895594328147163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1216895594328147163/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14868591585099/1000000000000000 : ℝ)*(2/5 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14868591585099/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264868591585099/1250000000000000 : ℝ) by norm_num, show 1+2*(1216895594328147163/50000000000000000000 : ℝ)=(26216895594328147163/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14868591585099/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14868591585099/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14868591585099/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14868591585099/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14868591585099/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14868591585099/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-950511603/5000000000 : ℝ)*X 0 0+(757632147/1250000000 : ℝ)*X 0 1+(4776793653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518427019/10000000000 : ℝ)*X 1 0+(-1319439001/5000000000 : ℝ)*X 1 1+(955358743/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5518427197/10000000000 : ℝ)*X 2 0+(597099193/1250000000 : ℝ)*X 2 1+(-2638877983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4203346651/10000000000 : ℝ)*X 0 0+(1561230131/5000000000 : ℝ)*X 0 1+(5662944357/10000000000 : ℝ)*X 0 2+(4203346651/10000000000 : ℝ)*X 1 0+(1561230131/5000000000 : ℝ)*X 1 1+(5662944357/10000000000 : ℝ)*X 1 2+(4203346651/10000000000 : ℝ)*X 2 0+(1561230131/5000000000 : ℝ)*X 2 1+(5662944357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-76250233/400000000 : ℝ)*X 0 0+(300621123/625000000 : ℝ)*X 0 1+(602674907/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646200937/1250000000 : ℝ)*X 1 0+(-1388923433/10000000000 : ℝ)*X 1 1+(753343941/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033922133/2000000000 : ℝ)*X 2 0+(1506687391/2500000000 : ℝ)*X 2 1+(-1388921737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4213694177/10000000000 : ℝ)*X 0 0+(5597382219/10000000000 : ℝ)*X 0 1+(79758099/250000000 : ℝ)*X 0 2+(4213694177/10000000000 : ℝ)*X 1 0+(5597382219/10000000000 : ℝ)*X 1 1+(79758099/250000000 : ℝ)*X 1 2+(4213694177/10000000000 : ℝ)*X 2 0+(5597382219/10000000000 : ℝ)*X 2 1+(79758099/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2872260233026377795441/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16770681/100000000000000 : ℝ)*(base1) + (176212921/50000000000000 : ℝ)*(base19) + (173683561/50000000000000 : ℝ)*(base23) + (15087387/50000000000000 : ℝ)*(base24) + (1365591/1562500000000 : ℝ)*(upper3) + (117228510954847/20000000000000 : ℝ)*(major0) + (117228510954847/20000000000000 : ℝ)*(major1) + (117228510954847/20000000000000 : ℝ)*(major2) + (48666096489653/6250000000000 : ℝ)*(sp0) + (778657922649691/100000000000000 : ℝ)*(sp1) + (389328948766819/50000000000000 : ℝ)*(sp2) + (98406530689327/25000000000000 : ℝ)*(sp3) + (748011767/100000000000000 : ℝ)*(sp4) + (647073937/100000000000000 : ℝ)*(sp7) + (393626786601927/100000000000000 : ℝ)*(f.failure) + (778658275075533/100000000000000 : ℝ)*(f.sum) + (23937274084853/10000000000000000000000000000 : ℝ)*base65 + (10987962964853/20000000000000000000000000000 : ℝ)*base67 + (57497612824853/20000000000000000000000000000 : ℝ)*base69 + (68454917304853/20000000000000000000000000000 : ℝ)*base71 + (20939511854853/10000000000000000000000000000 : ℝ)*base73 + (87297076204853/20000000000000000000000000000 : ℝ)*base75 + (62951886164853/20000000000000000000000000000 : ℝ)*base77 + (15227332395147/20000000000000000000000000000 : ℝ)*base80 + (80025253804853/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3551227/5000000000000000000000 : ℝ)*base90 + (3551227/5000000000000000000000 : ℝ)*base92 + (3551227/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95070176978782580350047/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (516770983/50000000000000 : ℝ)*(base19) + (1021483271/50000000000000 : ℝ)*(base23) + (458360791/100000000000000 : ℝ)*(base39) + (184133843/50000000000000 : ℝ)*(base45) + (244386231/100000000000000 : ℝ)*(upper3) + (78849689/25000000000000 : ℝ)*(upper5) + (618629349253787/100000000000000 : ℝ)*(major0) + (618629349253787/100000000000000 : ℝ)*(major1) + (154657222723249/25000000000000 : ℝ)*(major2) + (28006307/3125000000000 : ℝ)*(sp2) + (821814540555067/100000000000000 : ℝ)*(sp4) + (821813507013101/100000000000000 : ℝ)*(sp5) + (205453014936873/25000000000000 : ℝ)*(sp6) + (415443446071241/100000000000000 : ℝ)*(sp7) + (415443446071241/100000000000000 : ℝ)*(f.failure) + (410907499457929/50000000000000 : ℝ)*(f.sum) + (202759557386517/100000000000000000000000000000 : ℝ)*base65 + (26538381608349/25000000000000000000000000000 : ℝ)*base68 + (7804046480087/100000000000000000000000000000 : ℝ)*base70 + (1213590441651/25000000000000000000000000000 : ℝ)*base71 + (459067590986517/100000000000000000000000000000 : ℝ)*base73 + (791977110280087/100000000000000000000000000000 : ℝ)*base76 + (186444157980087/100000000000000000000000000000 : ℝ)*base78 + (86874993780087/100000000000000000000000000000 : ℝ)*base80 + (28665170319913/50000000000000000000000000000 : ℝ)*base81 + (11533141/5000000000000000000000 : ℝ)*base90 + (11533141/5000000000000000000000 : ℝ)*base92 + (11533141/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1113_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (147/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27927/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1113_s1_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053888043/5000000000 : ℝ)*x 0 + (178416759/312500000 : ℝ)*x 1 + (2498069363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053888043/5000000000 : ℝ)^4153 ≤ (12663055845201/100000000000000 : ℝ)^3129 := by
    have hnat : (1053888043 : ℕ)^4153*100000000000000^3129 ≤ 12663055845201^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053888043 5000000000 12663055845201 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178416759/312500000 : ℝ)^4153 ≤ (23762688277561/50000000000000 : ℝ)^3129 := by
    have hnat : (178416759 : ℕ)^4153*50000000000000^3129 ≤ 23762688277561^3129*312500000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178416759 312500000 23762688277561 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2498069363/5000000000 : ℝ)^4153 ≤ (39811567585299/100000000000000 : ℝ)^3129 := by
    have hnat : (2498069363 : ℕ)^4153*100000000000000^3129 ≤ 39811567585299^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498069363 5000000000 39811567585299 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053888043/5000000000 : ℝ), (178416759/312500000 : ℝ), (2498069363/5000000000 : ℝ)] ![(12663055845201/100000000000000 : ℝ), (23762688277561/50000000000000 : ℝ), (39811567585299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053888043/5000000000 : ℝ)|^4153 ≤ (12663055845201/100000000000000 : ℝ)^3129
        have hw : |(-1053888043/5000000000 : ℝ)|=(1053888043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(178416759/312500000 : ℝ)|^4153 ≤ (23762688277561/50000000000000 : ℝ)^3129
        have hw : |(178416759/312500000 : ℝ)|=(178416759/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2498069363/5000000000 : ℝ)|^4153 ≤ (39811567585299/100000000000000 : ℝ)^3129
        have hw : |(2498069363/5000000000 : ℝ)|=(2498069363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s1_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420720273/10000000000 : ℝ)*x 0 + (-1246615577/5000000000 : ℝ)*x 1 + (4996138651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420720273/10000000000 : ℝ)^4153 ≤ (22181667953823/50000000000000 : ℝ)^3129 := by
    have hnat : (5420720273 : ℕ)^4153*50000000000000^3129 ≤ 22181667953823^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420720273 10000000000 22181667953823 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246615577/5000000000 : ℝ)^4153 ≤ (3956274319721/25000000000000 : ℝ)^3129 := by
    have hnat : (1246615577 : ℕ)^4153*25000000000000^3129 ≤ 3956274319721^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246615577 5000000000 3956274319721 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4996138651/10000000000 : ℝ)^4153 ≤ (39811566792081/100000000000000 : ℝ)^3129 := by
    have hnat : (4996138651 : ℕ)^4153*100000000000000^3129 ≤ 39811566792081^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996138651 10000000000 39811566792081 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420720273/10000000000 : ℝ), (-1246615577/5000000000 : ℝ), (4996138651/10000000000 : ℝ)] ![(22181667953823/50000000000000 : ℝ), (3956274319721/25000000000000 : ℝ), (39811566792081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420720273/10000000000 : ℝ)|^4153 ≤ (22181667953823/50000000000000 : ℝ)^3129
        have hw : |(5420720273/10000000000 : ℝ)|=(5420720273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1246615577/5000000000 : ℝ)|^4153 ≤ (3956274319721/25000000000000 : ℝ)^3129
        have hw : |(-1246615577/5000000000 : ℝ)|=(1246615577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4996138651/10000000000 : ℝ)|^4153 ≤ (39811566792081/100000000000000 : ℝ)^3129
        have hw : |(4996138651/10000000000 : ℝ)|=(4996138651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s1_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420721621/10000000000 : ℝ)*x 0 + (999227477/2000000000 : ℝ)*x 1 + (-1246615503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420721621/10000000000 : ℝ)^4153 ≤ (44363350550087/100000000000000 : ℝ)^3129 := by
    have hnat : (5420721621 : ℕ)^4153*100000000000000^3129 ≤ 44363350550087^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420721621 10000000000 44363350550087 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999227477/2000000000 : ℝ)^4153 ≤ (19905776701283/50000000000000 : ℝ)^3129 := by
    have hnat : (999227477 : ℕ)^4153*50000000000000^3129 ≤ 19905776701283^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999227477 2000000000 19905776701283 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1246615503/5000000000 : ℝ)^4153 ≤ (15825096032069/100000000000000 : ℝ)^3129 := by
    have hnat : (1246615503 : ℕ)^4153*100000000000000^3129 ≤ 15825096032069^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246615503 5000000000 15825096032069 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420721621/10000000000 : ℝ), (999227477/2000000000 : ℝ), (-1246615503/5000000000 : ℝ)] ![(44363350550087/100000000000000 : ℝ), (19905776701283/50000000000000 : ℝ), (15825096032069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420721621/10000000000 : ℝ)|^4153 ≤ (44363350550087/100000000000000 : ℝ)^3129
        have hw : |(5420721621/10000000000 : ℝ)|=(5420721621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999227477/2000000000 : ℝ)|^4153 ≤ (19905776701283/50000000000000 : ℝ)^3129
        have hw : |(999227477/2000000000 : ℝ)|=(999227477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1246615503/5000000000 : ℝ)|^4153 ≤ (15825096032069/100000000000000 : ℝ)^3129
        have hw : |(-1246615503/5000000000 : ℝ)|=(1246615503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s1_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863976609/2000000000 : ℝ)*x 0 + (3671552703/10000000000 : ℝ)*x 1 + (5082372761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863976609/2000000000 : ℝ)^4153 ≤ (128214216789/390625000000 : ℝ)^3129 := by
    have hnat : (863976609 : ℕ)^4153*390625000000^3129 ≤ 128214216789^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863976609 2000000000 128214216789 390625000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3671552703/10000000000 : ℝ)^4153 ≤ (26450995405687/100000000000000 : ℝ)^3129 := by
    have hnat : (3671552703 : ℕ)^4153*100000000000000^3129 ≤ 26450995405687^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3671552703 10000000000 26450995405687 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082372761/10000000000 : ℝ)^4153 ≤ (636346329389/1562500000000 : ℝ)^3129 := by
    have hnat : (5082372761 : ℕ)^4153*1562500000000^3129 ≤ 636346329389^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082372761 10000000000 636346329389 1562500000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863976609/2000000000 : ℝ), (3671552703/10000000000 : ℝ), (5082372761/10000000000 : ℝ)] ![(128214216789/390625000000 : ℝ), (26450995405687/100000000000000 : ℝ), (636346329389/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863976609/2000000000 : ℝ)|^4153 ≤ (128214216789/390625000000 : ℝ)^3129
        have hw : |(863976609/2000000000 : ℝ)|=(863976609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3671552703/10000000000 : ℝ)|^4153 ≤ (26450995405687/100000000000000 : ℝ)^3129
        have hw : |(3671552703/10000000000 : ℝ)|=(3671552703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5082372761/10000000000 : ℝ)|^4153 ≤ (636346329389/1562500000000 : ℝ)^3129
        have hw : |(5082372761/10000000000 : ℝ)|=(5082372761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s1_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108623603/10000000000 : ℝ)*x 0 + (2502992699/5000000000 : ℝ)*x 1 + (5699292707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108623603/10000000000 : ℝ)^4153 ≤ (2533962859977/20000000000000 : ℝ)^3129 := by
    have hnat : (2108623603 : ℕ)^4153*20000000000000^3129 ≤ 2533962859977^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108623603 10000000000 2533962859977 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502992699/5000000000 : ℝ)^4153 ≤ (19957870943889/50000000000000 : ℝ)^3129 := by
    have hnat : (2502992699 : ℕ)^4153*50000000000000^3129 ≤ 19957870943889^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502992699 5000000000 19957870943889 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5699292707/10000000000 : ℝ)^4153 ≤ (47414443795387/100000000000000 : ℝ)^3129 := by
    have hnat : (5699292707 : ℕ)^4153*100000000000000^3129 ≤ 47414443795387^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5699292707 10000000000 47414443795387 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108623603/10000000000 : ℝ), (2502992699/5000000000 : ℝ), (5699292707/10000000000 : ℝ)] ![(2533962859977/20000000000000 : ℝ), (19957870943889/50000000000000 : ℝ), (47414443795387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108623603/10000000000 : ℝ)|^4153 ≤ (2533962859977/20000000000000 : ℝ)^3129
        have hw : |(-2108623603/10000000000 : ℝ)|=(2108623603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2502992699/5000000000 : ℝ)|^4153 ≤ (19957870943889/50000000000000 : ℝ)^3129
        have hw : |(2502992699/5000000000 : ℝ)|=(2502992699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5699292707/10000000000 : ℝ)|^4153 ≤ (47414443795387/100000000000000 : ℝ)^3129
        have hw : |(5699292707/10000000000 : ℝ)|=(5699292707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s1_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2619068413/5000000000 : ℝ)*x 0 + (-358015347/2000000000 : ℝ)*x 1 + (1139858501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619068413/5000000000 : ℝ)^4153 ≤ (4239106622511/10000000000000 : ℝ)^3129 := by
    have hnat : (2619068413 : ℕ)^4153*10000000000000^3129 ≤ 4239106622511^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619068413 5000000000 4239106622511 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358015347/2000000000 : ℝ)^4153 ≤ (2038898438799/20000000000000 : ℝ)^3129 := by
    have hnat : (358015347 : ℕ)^4153*20000000000000^3129 ≤ 2038898438799^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358015347 2000000000 2038898438799 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139858501/2000000000 : ℝ)^4153 ≤ (2963402597807/6250000000000 : ℝ)^3129 := by
    have hnat : (1139858501 : ℕ)^4153*6250000000000^3129 ≤ 2963402597807^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139858501 2000000000 2963402597807 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619068413/5000000000 : ℝ), (-358015347/2000000000 : ℝ), (1139858501/2000000000 : ℝ)] ![(4239106622511/10000000000000 : ℝ), (2038898438799/20000000000000 : ℝ), (2963402597807/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619068413/5000000000 : ℝ)|^4153 ≤ (4239106622511/10000000000000 : ℝ)^3129
        have hw : |(2619068413/5000000000 : ℝ)|=(2619068413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-358015347/2000000000 : ℝ)|^4153 ≤ (2038898438799/20000000000000 : ℝ)^3129
        have hw : |(-358015347/2000000000 : ℝ)|=(358015347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139858501/2000000000 : ℝ)|^4153 ≤ (2963402597807/6250000000000 : ℝ)^3129
        have hw : |(1139858501/2000000000 : ℝ)|=(1139858501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s1_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1047627371/2000000000 : ℝ)*x 0 + (113985853/200000000 : ℝ)*x 1 + (-895038241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047627371/2000000000 : ℝ)^4153 ≤ (8478213307321/20000000000000 : ℝ)^3129 := by
    have hnat : (1047627371 : ℕ)^4153*20000000000000^3129 ≤ 8478213307321^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047627371 2000000000 8478213307321 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113985853/200000000 : ℝ)^4153 ≤ (11853610791499/25000000000000 : ℝ)^3129 := by
    have hnat : (113985853 : ℕ)^4153*25000000000000^3129 ≤ 11853610791499^3129*200000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113985853 200000000 11853610791499 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895038241/5000000000 : ℝ)^4153 ≤ (1019449028163/10000000000000 : ℝ)^3129 := by
    have hnat : (895038241 : ℕ)^4153*10000000000000^3129 ≤ 1019449028163^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895038241 5000000000 1019449028163 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047627371/2000000000 : ℝ), (113985853/200000000 : ℝ), (-895038241/5000000000 : ℝ)] ![(8478213307321/20000000000000 : ℝ), (11853610791499/25000000000000 : ℝ), (1019449028163/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047627371/2000000000 : ℝ)|^4153 ≤ (8478213307321/20000000000000 : ℝ)^3129
        have hw : |(1047627371/2000000000 : ℝ)|=(1047627371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113985853/200000000 : ℝ)|^4153 ≤ (11853610791499/25000000000000 : ℝ)^3129
        have hw : |(113985853/200000000 : ℝ)|=(113985853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-895038241/5000000000 : ℝ)|^4153 ≤ (1019449028163/10000000000000 : ℝ)^3129
        have hw : |(-895038241/5000000000 : ℝ)|=(895038241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s1_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321557821/10000000000 : ℝ)*x 0 + (5062895169/10000000000 : ℝ)*x 1 + (1845709837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321557821/10000000000 : ℝ)^4153 ≤ (4104966260921/12500000000000 : ℝ)^3129 := by
    have hnat : (4321557821 : ℕ)^4153*12500000000000^3129 ≤ 4104966260921^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321557821 10000000000 4104966260921 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5062895169/10000000000 : ℝ)^4153 ≤ (810382771321/2000000000000 : ℝ)^3129 := by
    have hnat : (5062895169 : ℕ)^4153*2000000000000^3129 ≤ 810382771321^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062895169 10000000000 810382771321 2000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1845709837/5000000000 : ℝ)^4153 ≤ (3330141415923/12500000000000 : ℝ)^3129 := by
    have hnat : (1845709837 : ℕ)^4153*12500000000000^3129 ≤ 3330141415923^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845709837 5000000000 3330141415923 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321557821/10000000000 : ℝ), (5062895169/10000000000 : ℝ), (1845709837/5000000000 : ℝ)] ![(4104966260921/12500000000000 : ℝ), (810382771321/2000000000000 : ℝ), (3330141415923/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321557821/10000000000 : ℝ)|^4153 ≤ (4104966260921/12500000000000 : ℝ)^3129
        have hw : |(4321557821/10000000000 : ℝ)|=(4321557821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5062895169/10000000000 : ℝ)|^4153 ≤ (810382771321/2000000000000 : ℝ)^3129
        have hw : |(5062895169/10000000000 : ℝ)|=(5062895169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1845709837/5000000000 : ℝ)|^4153 ≤ (3330141415923/12500000000000 : ℝ)^3129
        have hw : |(1845709837/5000000000 : ℝ)|=(1845709837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27927/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2743/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2057/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27927/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (147/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27927/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (147/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27927/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (147/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27927/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (147/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27927/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (147/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27927/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (147/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (147/50000 : ℝ) ^ (8305/2048 : ℝ) ≤ (5416308687/100000000000000000000 : ℝ) := by
    have hpowers : (147/50000 : ℝ)^8305 ≤ (5416308687/100000000000000000000 : ℝ)^2048 := by
      have hnat : (147 : ℕ)^8305*100000000000000000000^2048 ≤ 5416308687^2048*50000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 50000 5416308687 100000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/50000 : ℝ)) (X := (5416308687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27927/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (141733041171620399/25000000000000000000 : ℝ) := by
    have hpowers : (27927/100000 : ℝ)^8305 ≤ (141733041171620399/25000000000000000000 : ℝ)^2048 := by
      have hnat : (27927 : ℕ)^8305*25000000000000000000^2048 ≤ 141733041171620399^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27927 100000 141733041171620399 25000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27927/100000 : ℝ)) (X := (141733041171620399/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000005416308687/50000000000000000000 : ℝ) ≤ (10000000000267131/10000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50000000005416308687/50000000000000000000 : ℝ)^2048 ≤ (10000000000267131/10000000000000000 : ℝ)^8305 := by
      have hnat : (50000000005416308687 : ℕ)^2048*10000000000000000^8305 ≤ 10000000000267131^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000005416308687 50000000000000000000 10000000000267131 10000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000267131/10000000000000000 : ℝ)) (X := (50000000005416308687/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100566932170102790283/100000000000000000000 : ℝ) ≤ (5006975349961223/5000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (100566932170102790283/100000000000000000000 : ℝ)^2048 ≤ (5006975349961223/5000000000000000 : ℝ)^8305 := by
      have hnat : (100566932170102790283 : ℕ)^2048*5000000000000000^8305 ≤ 5006975349961223^8305*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100566932170102790283 100000000000000000000 5006975349961223 5000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006975349961223/5000000000000000 : ℝ)) (X := (100566932170102790283/100000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12641733041171620399/12500000000000000000 : ℝ) ≤ (10027901399577761/10000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (12641733041171620399/12500000000000000000 : ℝ)^2048 ≤ (10027901399577761/10000000000000000 : ℝ)^8305 := by
      have hnat : (12641733041171620399 : ℕ)^2048*10000000000000000^8305 ≤ 10027901399577761^8305*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12641733041171620399 12500000000000000000 10027901399577761 10000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027901399577761/10000000000000000 : ℝ)) (X := (12641733041171620399/12500000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5416308687/100000000000000000000 : ℝ) ≤ ((92107265665328101901/92110000000000000000 : ℝ)+2*(2790139931063/552660000000000 : ℝ)*(147/50000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (92107265665328101901/92110000000000000000 : ℝ)+2*(2790139931063/552660000000000 : ℝ)*(147/50000 : ℝ)=(10000000000267131/10000000000000000 : ℝ) by norm_num, show 1+2*(5416308687/100000000000000000000 : ℝ)=(50000000005416308687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(141733041171620399/25000000000000000000 : ℝ)+(5416308687/100000000000000000000 : ℝ) ≤ ((92107265665328101901/92110000000000000000 : ℝ)+(2790139931063/552660000000000 : ℝ)*((27927/100000 : ℝ)+(147/50000 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (92107265665328101901/92110000000000000000 : ℝ)+(2790139931063/552660000000000 : ℝ)*((27927/100000 : ℝ)+(147/50000 : ℝ))=(5006975349961223/5000000000000000 : ℝ) by norm_num, show 1+(141733041171620399/25000000000000000000 : ℝ)+(5416308687/100000000000000000000 : ℝ)=(100566932170102790283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(141733041171620399/25000000000000000000 : ℝ) ≤ ((92107265665328101901/92110000000000000000 : ℝ)+2*(2790139931063/552660000000000 : ℝ)*(27927/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (92107265665328101901/92110000000000000000 : ℝ)+2*(2790139931063/552660000000000 : ℝ)*(27927/100000 : ℝ)=(10027901399577761/10000000000000000 : ℝ) by norm_num, show 1+2*(141733041171620399/25000000000000000000 : ℝ)=(12641733041171620399/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92107265665328101901/92110000000000000000 : ℝ)*(X 1 0+X 2 0)+(2790139931063/552660000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (147/50000 : ℝ)) (hi := (27927/100000 : ℝ)) (c := (92107265665328101901/92110000000000000000 : ℝ)) (alpha := (2790139931063/552660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92107265665328101901/92110000000000000000 : ℝ)*(X 0 1+X 2 1)+(2790139931063/552660000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (147/50000 : ℝ)) (hi := (27927/100000 : ℝ)) (c := (92107265665328101901/92110000000000000000 : ℝ)) (alpha := (2790139931063/552660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92107265665328101901/92110000000000000000 : ℝ)*(X 0 2+X 1 2)+(2790139931063/552660000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (147/50000 : ℝ)) (hi := (27927/100000 : ℝ)) (c := (92107265665328101901/92110000000000000000 : ℝ)) (alpha := (2790139931063/552660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1053888043/5000000000 : ℝ)*X 0 0+(178416759/312500000 : ℝ)*X 0 1+(2498069363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420720273/10000000000 : ℝ)*X 1 0+(-1246615577/5000000000 : ℝ)*X 1 1+(4996138651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420721621/10000000000 : ℝ)*X 2 0+(999227477/2000000000 : ℝ)*X 2 1+(-1246615503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863976609/2000000000 : ℝ)*X 0 0+(3671552703/10000000000 : ℝ)*X 0 1+(5082372761/10000000000 : ℝ)*X 0 2+(863976609/2000000000 : ℝ)*X 1 0+(3671552703/10000000000 : ℝ)*X 1 1+(5082372761/10000000000 : ℝ)*X 1 2+(863976609/2000000000 : ℝ)*X 2 0+(3671552703/10000000000 : ℝ)*X 2 1+(5082372761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108623603/10000000000 : ℝ)*X 0 0+(2502992699/5000000000 : ℝ)*X 0 1+(5699292707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2619068413/5000000000 : ℝ)*X 1 0+(-358015347/2000000000 : ℝ)*X 1 1+(1139858501/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047627371/2000000000 : ℝ)*X 2 0+(113985853/200000000 : ℝ)*X 2 1+(-895038241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321557821/10000000000 : ℝ)*X 0 0+(5062895169/10000000000 : ℝ)*X 0 1+(1845709837/5000000000 : ℝ)*X 0 2+(4321557821/10000000000 : ℝ)*X 1 0+(5062895169/10000000000 : ℝ)*X 1 1+(1845709837/5000000000 : ℝ)*X 1 2+(4321557821/10000000000 : ℝ)*X 2 0+(5062895169/10000000000 : ℝ)*X 2 1+(1845709837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (997521355789443371157721477/460550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98796787/50000000000000 : ℝ)*(base1) + (208307051/100000000000000 : ℝ)*(base19) + (592226669/100000000000000 : ℝ)*(base23) + (4815161/12500000000000 : ℝ)*(base37) + (11152697/50000000000000 : ℝ)*(upper3) + (105547190304941/10000000000000 : ℝ)*(major0) + (105547190304941/10000000000000 : ℝ)*(major1) + (105547190304941/10000000000000 : ℝ)*(major2) + (701068078996081/50000000000000 : ℝ)*(sp0) + (280427072745527/20000000000000 : ℝ)*(sp1) + (1402136026132287/100000000000000 : ℝ)*(sp2) + (177201719856791/25000000000000 : ℝ)*(sp3) + (657960369/100000000000000 : ℝ)*(sp4) + (104632427/10000000000000 : ℝ)*(sp5) + (708807115542027/100000000000000 : ℝ)*(f.failure) + (350534154589739/25000000000000 : ℝ)*(f.sum) + (66123966022177/27633000000000000000000000000 : ℝ)*base65 + (2759810559396121477/2763300000000000000000000000000000 : ℝ)*base68 + (4007671214549821477/2763300000000000000000000000000000 : ℝ)*base70 + (167753961085378523/2763300000000000000000000000000000 : ℝ)*base71 + (24699986980457/13816500000000000000000000000 : ℝ)*base73 + (15441754379658178523/2763300000000000000000000000000000 : ℝ)*base75 + (3959924912253778523/2763300000000000000000000000000000 : ℝ)*base77 + (12069762260259778523/2763300000000000000000000000000000 : ℝ)*base79 + (9166920379981/6908250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (16918673/5000000000000000000000 : ℝ)*base89 + (16918673/5000000000000000000000 : ℝ)*base91 + (16918673/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2956062171821256220815034481/575687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6305793/10000000000000 : ℝ)*(base1) + (577079393/50000000000000 : ℝ)*(base19) + (1179691983/100000000000000 : ℝ)*(base23) + (55687659/50000000000000 : ℝ)*(upper3) + (28594567/25000000000000 : ℝ)*(upper5) + (135718989681473/12500000000000 : ℝ)*(major0) + (135718989681473/12500000000000 : ℝ)*(major1) + (135718989681473/12500000000000 : ℝ)*(major2) + (1137447891/25000000000000 : ℝ)*(sp1) + (5053184689/100000000000000 : ℝ)*(sp2) + (721180962659043/50000000000000 : ℝ)*(sp4) + (721178079154903/50000000000000 : ℝ)*(sp5) + (360588907345871/25000000000000 : ℝ)*(sp6) + (145828347684841/20000000000000 : ℝ)*(sp7) + (145828360296427/20000000000000 : ℝ)*(f.failure) + (360590465565039/25000000000000 : ℝ)*(f.sum) + (7273693805441/27633000000000000000000000000 : ℝ)*base65 + (13254941063350715519/3454125000000000000000000000000000 : ℝ)*base67 + (6213661456357659481/3454125000000000000000000000000000 : ℝ)*base70 + (5218673327809284481/3454125000000000000000000000000000 : ℝ)*base72 + (17802731426497/5526600000000000000000000000 : ℝ)*base73 + (23136227291500340519/3454125000000000000000000000000000 : ℝ)*base75 + (3718975414026590519/3454125000000000000000000000000000 : ℝ)*base77 + (22257141612323090519/3454125000000000000000000000000000 : ℝ)*base79 + (23443978099273/6908250000000000000000000000 : ℝ)*base82 + (5204273/1000000000000000000000 : ℝ)*base89 + (5204273/1000000000000000000000 : ℝ)*base91 + (5204273/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1113_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27927/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2057/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1113_s2_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081292923/5000000000 : ℝ)*x 0 + (2758208063/5000000000 : ℝ)*x 1 + (644279511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081292923/5000000000 : ℝ)^4153 ≤ (13101951921181/100000000000000 : ℝ)^3129 := by
    have hnat : (1081292923 : ℕ)^4153*100000000000000^3129 ≤ 13101951921181^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081292923 5000000000 13101951921181 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758208063/5000000000 : ℝ)^4153 ≤ (45405808152683/100000000000000 : ℝ)^3129 := by
    have hnat : (2758208063 : ℕ)^4153*100000000000000^3129 ≤ 45405808152683^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758208063 5000000000 45405808152683 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644279511/1250000000 : ℝ)^4153 ≤ (1296632497147/3125000000000 : ℝ)^3129 := by
    have hnat : (644279511 : ℕ)^4153*3125000000000^3129 ≤ 1296632497147^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644279511 1250000000 1296632497147 3125000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081292923/5000000000 : ℝ), (2758208063/5000000000 : ℝ), (644279511/1250000000 : ℝ)] ![(13101951921181/100000000000000 : ℝ), (45405808152683/100000000000000 : ℝ), (1296632497147/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081292923/5000000000 : ℝ)|^4153 ≤ (13101951921181/100000000000000 : ℝ)^3129
        have hw : |(-1081292923/5000000000 : ℝ)|=(1081292923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758208063/5000000000 : ℝ)|^4153 ≤ (45405808152683/100000000000000 : ℝ)^3129
        have hw : |(2758208063/5000000000 : ℝ)|=(2758208063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644279511/1250000000 : ℝ)|^4153 ≤ (1296632497147/3125000000000 : ℝ)^3129
        have hw : |(644279511/1250000000 : ℝ)|=(644279511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s2_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375120963/10000000000 : ℝ)*x 0 + (-1175550167/5000000000 : ℝ)*x 1 + (5154237407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375120963/10000000000 : ℝ)^4153 ≤ (21934351787847/50000000000000 : ℝ)^3129 := by
    have hnat : (5375120963 : ℕ)^4153*50000000000000^3129 ≤ 21934351787847^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375120963 10000000000 21934351787847 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1175550167/5000000000 : ℝ)^4153 ≤ (14639042404937/100000000000000 : ℝ)^3129 := by
    have hnat : (1175550167 : ℕ)^4153*100000000000000^3129 ≤ 14639042404937^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175550167 5000000000 14639042404937 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5154237407/10000000000 : ℝ)^4153 ≤ (20746127000857/50000000000000 : ℝ)^3129 := by
    have hnat : (5154237407 : ℕ)^4153*50000000000000^3129 ≤ 20746127000857^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154237407 10000000000 20746127000857 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375120963/10000000000 : ℝ), (-1175550167/5000000000 : ℝ), (5154237407/10000000000 : ℝ)] ![(21934351787847/50000000000000 : ℝ), (14639042404937/100000000000000 : ℝ), (20746127000857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375120963/10000000000 : ℝ)|^4153 ≤ (21934351787847/50000000000000 : ℝ)^3129
        have hw : |(5375120963/10000000000 : ℝ)|=(5375120963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1175550167/5000000000 : ℝ)|^4153 ≤ (14639042404937/100000000000000 : ℝ)^3129
        have hw : |(-1175550167/5000000000 : ℝ)|=(1175550167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5154237407/10000000000 : ℝ)|^4153 ≤ (20746127000857/50000000000000 : ℝ)^3129
        have hw : |(5154237407/10000000000 : ℝ)|=(5154237407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s2_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375120903/10000000000 : ℝ)*x 0 + (2577118733/5000000000 : ℝ)*x 1 + (-2351100337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375120903/10000000000 : ℝ)^4153 ≤ (5483587865719/12500000000000 : ℝ)^3129 := by
    have hnat : (5375120903 : ℕ)^4153*12500000000000^3129 ≤ 5483587865719^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375120903 10000000000 5483587865719 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577118733/5000000000 : ℝ)^4153 ≤ (20746127316053/50000000000000 : ℝ)^3129 := by
    have hnat : (2577118733 : ℕ)^4153*50000000000000^3129 ≤ 20746127316053^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577118733 5000000000 20746127316053 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2351100337/10000000000 : ℝ)^4153 ≤ (1463904242973/10000000000000 : ℝ)^3129 := by
    have hnat : (2351100337 : ℕ)^4153*10000000000000^3129 ≤ 1463904242973^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351100337 10000000000 1463904242973 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375120903/10000000000 : ℝ), (2577118733/5000000000 : ℝ), (-2351100337/10000000000 : ℝ)] ![(5483587865719/12500000000000 : ℝ), (20746127316053/50000000000000 : ℝ), (1463904242973/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375120903/10000000000 : ℝ)|^4153 ≤ (5483587865719/12500000000000 : ℝ)^3129
        have hw : |(5375120903/10000000000 : ℝ)|=(5375120903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577118733/5000000000 : ℝ)|^4153 ≤ (20746127316053/50000000000000 : ℝ)^3129
        have hw : |(2577118733/5000000000 : ℝ)|=(2577118733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2351100337/10000000000 : ℝ)|^4153 ≤ (1463904242973/10000000000000 : ℝ)^3129
        have hw : |(-2351100337/10000000000 : ℝ)|=(2351100337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s2_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4357407741/10000000000 : ℝ)*x 0 + (4013873581/10000000000 : ℝ)*x 1 + (4730322029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357407741/10000000000 : ℝ)^4153 ≤ (1328071979947/4000000000000 : ℝ)^3129 := by
    have hnat : (4357407741 : ℕ)^4153*4000000000000^3129 ≤ 1328071979947^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357407741 10000000000 1328071979947 4000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013873581/10000000000 : ℝ)^4153 ≤ (14886599660193/50000000000000 : ℝ)^3129 := by
    have hnat : (4013873581 : ℕ)^4153*50000000000000^3129 ≤ 14886599660193^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013873581 10000000000 14886599660193 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4730322029/10000000000 : ℝ)^4153 ≤ (37025001168517/100000000000000 : ℝ)^3129 := by
    have hnat : (4730322029 : ℕ)^4153*100000000000000^3129 ≤ 37025001168517^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730322029 10000000000 37025001168517 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357407741/10000000000 : ℝ), (4013873581/10000000000 : ℝ), (4730322029/10000000000 : ℝ)] ![(1328071979947/4000000000000 : ℝ), (14886599660193/50000000000000 : ℝ), (37025001168517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357407741/10000000000 : ℝ)|^4153 ≤ (1328071979947/4000000000000 : ℝ)^3129
        have hw : |(4357407741/10000000000 : ℝ)|=(4357407741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013873581/10000000000 : ℝ)|^4153 ≤ (14886599660193/50000000000000 : ℝ)^3129
        have hw : |(4013873581/10000000000 : ℝ)|=(4013873581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4730322029/10000000000 : ℝ)|^4153 ≤ (37025001168517/100000000000000 : ℝ)^3129
        have hw : |(4730322029/10000000000 : ℝ)|=(4730322029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s2_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-540674123/2500000000 : ℝ)*x 0 + (1031357033/2000000000 : ℝ)*x 1 + (1102768247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540674123/2500000000 : ℝ)^4153 ≤ (13102841651453/100000000000000 : ℝ)^3129 := by
    have hnat : (540674123 : ℕ)^4153*100000000000000^3129 ≤ 13102841651453^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540674123 2500000000 13102841651453 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031357033/2000000000 : ℝ)^4153 ≤ (10379869505709/25000000000000 : ℝ)^3129 := by
    have hnat : (1031357033 : ℕ)^4153*25000000000000^3129 ≤ 10379869505709^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031357033 2000000000 10379869505709 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102768247/2000000000 : ℝ)^4153 ≤ (45377680309471/100000000000000 : ℝ)^3129 := by
    have hnat : (1102768247 : ℕ)^4153*100000000000000^3129 ≤ 45377680309471^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102768247 2000000000 45377680309471 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540674123/2500000000 : ℝ), (1031357033/2000000000 : ℝ), (1102768247/2000000000 : ℝ)] ![(13102841651453/100000000000000 : ℝ), (10379869505709/25000000000000 : ℝ), (45377680309471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540674123/2500000000 : ℝ)|^4153 ≤ (13102841651453/100000000000000 : ℝ)^3129
        have hw : |(-540674123/2500000000 : ℝ)|=(540674123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031357033/2000000000 : ℝ)|^4153 ≤ (10379869505709/25000000000000 : ℝ)^3129
        have hw : |(1031357033/2000000000 : ℝ)|=(1031357033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102768247/2000000000 : ℝ)|^4153 ≤ (45377680309471/100000000000000 : ℝ)^3129
        have hw : |(1102768247/2000000000 : ℝ)|=(1102768247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s2_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5283405449/10000000000 : ℝ)*x 0 + (-199149587/1000000000 : ℝ)*x 1 + (5513841317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283405449/10000000000 : ℝ)^4153 ≤ (42877993024909/100000000000000 : ℝ)^3129 := by
    have hnat : (5283405449 : ℕ)^4153*100000000000000^3129 ≤ 42877993024909^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283405449 10000000000 42877993024909 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199149587/1000000000 : ℝ)^4153 ≤ (11744325755763/100000000000000 : ℝ)^3129 := by
    have hnat : (199149587 : ℕ)^4153*100000000000000^3129 ≤ 11744325755763^3129*1000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199149587 1000000000 11744325755763 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513841317/10000000000 : ℝ)^4153 ≤ (22688840602581/50000000000000 : ℝ)^3129 := by
    have hnat : (5513841317 : ℕ)^4153*50000000000000^3129 ≤ 22688840602581^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513841317 10000000000 22688840602581 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283405449/10000000000 : ℝ), (-199149587/1000000000 : ℝ), (5513841317/10000000000 : ℝ)] ![(42877993024909/100000000000000 : ℝ), (11744325755763/100000000000000 : ℝ), (22688840602581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283405449/10000000000 : ℝ)|^4153 ≤ (42877993024909/100000000000000 : ℝ)^3129
        have hw : |(5283405449/10000000000 : ℝ)|=(5283405449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199149587/1000000000 : ℝ)|^4153 ≤ (11744325755763/100000000000000 : ℝ)^3129
        have hw : |(-199149587/1000000000 : ℝ)|=(199149587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513841317/10000000000 : ℝ)|^4153 ≤ (22688840602581/50000000000000 : ℝ)^3129
        have hw : |(5513841317/10000000000 : ℝ)|=(5513841317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s2_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2641702789/5000000000 : ℝ)*x 0 + (5513841267/10000000000 : ℝ)*x 1 + (-1991495763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641702789/5000000000 : ℝ)^4153 ≤ (8575598882887/20000000000000 : ℝ)^3129 := by
    have hnat : (2641702789 : ℕ)^4153*20000000000000^3129 ≤ 8575598882887^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641702789 5000000000 8575598882887 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513841267/10000000000 : ℝ)^4153 ≤ (45377680659009/100000000000000 : ℝ)^3129 := by
    have hnat : (5513841267 : ℕ)^4153*100000000000000^3129 ≤ 45377680659009^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513841267 10000000000 45377680659009 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991495763/10000000000 : ℝ)^4153 ≤ (2348864983651/20000000000000 : ℝ)^3129 := by
    have hnat : (1991495763 : ℕ)^4153*20000000000000^3129 ≤ 2348864983651^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991495763 10000000000 2348864983651 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641702789/5000000000 : ℝ), (5513841267/10000000000 : ℝ), (-1991495763/10000000000 : ℝ)] ![(8575598882887/20000000000000 : ℝ), (45377680659009/100000000000000 : ℝ), (2348864983651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641702789/5000000000 : ℝ)|^4153 ≤ (8575598882887/20000000000000 : ℝ)^3129
        have hw : |(2641702789/5000000000 : ℝ)|=(2641702789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513841267/10000000000 : ℝ)|^4153 ≤ (45377680659009/100000000000000 : ℝ)^3129
        have hw : |(5513841267/10000000000 : ℝ)|=(5513841267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991495763/10000000000 : ℝ)|^4153 ≤ (2348864983651/20000000000000 : ℝ)^3129
        have hw : |(-1991495763/10000000000 : ℝ)|=(1991495763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s2_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089407/2500000 : ℝ)*x 0 + (4725280813/10000000000 : ℝ)*x 1 + (2009482461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089407/2500000 : ℝ)^4153 ≤ (16602013523271/50000000000000 : ℝ)^3129 := by
    have hnat : (1089407 : ℕ)^4153*50000000000000^3129 ≤ 16602013523271^3129*2500000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089407 2500000 16602013523271 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4725280813/10000000000 : ℝ)^4153 ≤ (36972638678783/100000000000000 : ℝ)^3129 := by
    have hnat : (4725280813 : ℕ)^4153*100000000000000^3129 ≤ 36972638678783^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4725280813 10000000000 36972638678783 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009482461/5000000000 : ℝ)^4153 ≤ (14911667128677/50000000000000 : ℝ)^3129 := by
    have hnat : (2009482461 : ℕ)^4153*50000000000000^3129 ≤ 14911667128677^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009482461 5000000000 14911667128677 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089407/2500000 : ℝ), (4725280813/10000000000 : ℝ), (2009482461/5000000000 : ℝ)] ![(16602013523271/50000000000000 : ℝ), (36972638678783/100000000000000 : ℝ), (14911667128677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089407/2500000 : ℝ)|^4153 ≤ (16602013523271/50000000000000 : ℝ)^3129
        have hw : |(1089407/2500000 : ℝ)|=(1089407/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4725280813/10000000000 : ℝ)|^4153 ≤ (36972638678783/100000000000000 : ℝ)^3129
        have hw : |(4725280813/10000000000 : ℝ)|=(4725280813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2009482461/5000000000 : ℝ)|^4153 ≤ (14911667128677/50000000000000 : ℝ)^3129
        have hw : |(2009482461/5000000000 : ℝ)|=(2009482461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2057/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8937/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16591/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2057/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2743/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2057/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2743/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2057/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2743/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2057/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2743/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2057/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2743/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2057/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2743/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2743/50000 : ℝ) ^ (8305/2048 : ℝ) ≤ (192930404893179/25000000000000000000 : ℝ) := by
    have hpowers : (2743/50000 : ℝ)^8305 ≤ (192930404893179/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2743 : ℕ)^8305*25000000000000000000^2048 ≤ 192930404893179^2048*50000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2743 50000 192930404893179 25000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2743/50000 : ℝ)) (X := (192930404893179/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2057/10000 : ℝ) ^ (8305/2048 : ℝ) ≤ (164075725128805357/100000000000000000000 : ℝ) := by
    have hpowers : (2057/10000 : ℝ)^8305 ≤ (164075725128805357/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2057 : ℕ)^8305*100000000000000000000^2048 ≤ 164075725128805357^2048*10000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2057 10000 164075725128805357 100000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2057/10000 : ℝ)) (X := (164075725128805357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500192930404893179/12500000000000000000 : ℝ) ≤ (2500009515211847/2500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (12500192930404893179/12500000000000000000 : ℝ)^2048 ≤ (2500009515211847/2500000000000000 : ℝ)^8305 := by
      have hnat : (12500192930404893179 : ℕ)^2048*2500000000000000^8305 ≤ 2500009515211847^8305*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500192930404893179 12500000000000000000 2500009515211847 2500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009515211847/2500000000000000 : ℝ)) (X := (12500192930404893179/12500000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100164847446748378073/100000000000000000000 : ℝ) ≤ (312626955946947/312500000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (100164847446748378073/100000000000000000000 : ℝ)^2048 ≤ (312626955946947/312500000000000 : ℝ)^8305 := by
      have hnat : (100164847446748378073 : ℕ)^2048*312500000000000^8305 ≤ 312626955946947^8305*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100164847446748378073 100000000000000000000 312626955946947 312500000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312626955946947/312500000000000 : ℝ)) (X := (100164847446748378073/100000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50164075725128805357/50000000000000000000 : ℝ) ≤ (500404355987861/500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50164075725128805357/50000000000000000000 : ℝ)^2048 ≤ (500404355987861/500000000000000 : ℝ)^8305 := by
      have hnat : (50164075725128805357 : ℕ)^2048*500000000000000^8305 ≤ 500404355987861^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50164075725128805357 50000000000000000000 500404355987861 500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500404355987861/500000000000000 : ℝ)) (X := (50164075725128805357/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(192930404893179/25000000000000000000 : ℝ) ≤ ((942477606079016639/942750000000000000 : ℝ)+2*(1006132363729/377100000000000 : ℝ)*(2743/50000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (942477606079016639/942750000000000000 : ℝ)+2*(1006132363729/377100000000000 : ℝ)*(2743/50000 : ℝ)=(2500009515211847/2500000000000000 : ℝ) by norm_num, show 1+2*(192930404893179/25000000000000000000 : ℝ)=(12500192930404893179/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(164075725128805357/100000000000000000000 : ℝ)+(192930404893179/25000000000000000000 : ℝ) ≤ ((942477606079016639/942750000000000000 : ℝ)+(1006132363729/377100000000000 : ℝ)*((2057/10000 : ℝ)+(2743/50000 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (942477606079016639/942750000000000000 : ℝ)+(1006132363729/377100000000000 : ℝ)*((2057/10000 : ℝ)+(2743/50000 : ℝ))=(312626955946947/312500000000000 : ℝ) by norm_num, show 1+(164075725128805357/100000000000000000000 : ℝ)+(192930404893179/25000000000000000000 : ℝ)=(100164847446748378073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(164075725128805357/100000000000000000000 : ℝ) ≤ ((942477606079016639/942750000000000000 : ℝ)+2*(1006132363729/377100000000000 : ℝ)*(2057/10000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (942477606079016639/942750000000000000 : ℝ)+2*(1006132363729/377100000000000 : ℝ)*(2057/10000 : ℝ)=(500404355987861/500000000000000 : ℝ) by norm_num, show 1+2*(164075725128805357/100000000000000000000 : ℝ)=(50164075725128805357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (942477606079016639/942750000000000000 : ℝ)*(X 1 0+X 2 0)+(1006132363729/377100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (2743/50000 : ℝ)) (hi := (2057/10000 : ℝ)) (c := (942477606079016639/942750000000000000 : ℝ)) (alpha := (1006132363729/377100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (942477606079016639/942750000000000000 : ℝ)*(X 0 1+X 2 1)+(1006132363729/377100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (2743/50000 : ℝ)) (hi := (2057/10000 : ℝ)) (c := (942477606079016639/942750000000000000 : ℝ)) (alpha := (1006132363729/377100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (942477606079016639/942750000000000000 : ℝ)*(X 0 2+X 1 2)+(1006132363729/377100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (2743/50000 : ℝ)) (hi := (2057/10000 : ℝ)) (c := (942477606079016639/942750000000000000 : ℝ)) (alpha := (1006132363729/377100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1081292923/5000000000 : ℝ)*X 0 0+(2758208063/5000000000 : ℝ)*X 0 1+(644279511/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375120963/10000000000 : ℝ)*X 1 0+(-1175550167/5000000000 : ℝ)*X 1 1+(5154237407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375120903/10000000000 : ℝ)*X 2 0+(2577118733/5000000000 : ℝ)*X 2 1+(-2351100337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357407741/10000000000 : ℝ)*X 0 0+(4013873581/10000000000 : ℝ)*X 0 1+(4730322029/10000000000 : ℝ)*X 0 2+(4357407741/10000000000 : ℝ)*X 1 0+(4013873581/10000000000 : ℝ)*X 1 1+(4730322029/10000000000 : ℝ)*X 1 2+(4357407741/10000000000 : ℝ)*X 2 0+(4013873581/10000000000 : ℝ)*X 2 1+(4730322029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-540674123/2500000000 : ℝ)*X 0 0+(1031357033/2000000000 : ℝ)*X 0 1+(1102768247/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283405449/10000000000 : ℝ)*X 1 0+(-199149587/1000000000 : ℝ)*X 1 1+(5513841317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641702789/5000000000 : ℝ)*X 2 0+(5513841267/10000000000 : ℝ)*X 2 1+(-1991495763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089407/2500000 : ℝ)*X 0 0+(4725280813/10000000000 : ℝ)*X 0 1+(2009482461/5000000000 : ℝ)*X 0 2+(1089407/2500000 : ℝ)*X 1 0+(4725280813/10000000000 : ℝ)*X 1 1+(2009482461/5000000000 : ℝ)*X 1 2+(1089407/2500000 : ℝ)*X 2 0+(4725280813/10000000000 : ℝ)*X 2 1+(2009482461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27604459740371753456922553/3928125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21375453/3125000000000 : ℝ)*(base19) + (101345411/25000000000000 : ℝ)*(base23) + (2519167/50000000000000 : ℝ)*(upper2) + (7939897/4000000000000 : ℝ)*(upper3) + (138240341/100000000000000 : ℝ)*(upper4) + (519608830563841/25000000000000 : ℝ)*(major0) + (519608830563841/25000000000000 : ℝ)*(major1) + (519608830563841/25000000000000 : ℝ)*(major2) + (1380536789718273/50000000000000 : ℝ)*(sp0) + (345135840028681/12500000000000 : ℝ)*(sp1) + (27610869988623/1000000000000 : ℝ)*(sp2) + (1395777460474313/100000000000000 : ℝ)*(sp3) + (6912403699/50000000000000 : ℝ)*(sp4) + (5545546191/100000000000000 : ℝ)*(sp7) + (174472875752563/12500000000000 : ℝ)*(f.failure) + (345135925530493/12500000000000 : ℝ)*(f.sum) + (51096449707501/18855000000000000000000000000 : ℝ)*base65 + (12378906368481711/2618750000000000000000000000000 : ℝ)*base67 + (5756527162575461/2618750000000000000000000000000 : ℝ)*base69 + (289777597575461/2618750000000000000000000000000 : ℝ)*base71 + (5798502380141/4713750000000000000000000000 : ℝ)*base74 + (12618090127562961/2618750000000000000000000000000 : ℝ)*base75 + (16437151213550461/2618750000000000000000000000000 : ℝ)*base77 + (5313151368819211/2618750000000000000000000000000 : ℝ)*base79 + (51810913787189/18855000000000000000000000000 : ℝ)*base82 + (105737/625000000000000000000 : ℝ)*base89 + (105737/625000000000000000000 : ℝ)*base91 + (105737/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154659656921992376128283057/15712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (985122189/50000000000000 : ℝ)*(base19) + (2225272631/100000000000000 : ℝ)*(base23) + (253122723/100000000000000 : ℝ)*(upper3) + (70087457/100000000000000 : ℝ)*(lower4) + (194737111/100000000000000 : ℝ)*(upper5) + (2108238545126737/100000000000000 : ℝ)*(major0) + (2108238545126737/100000000000000 : ℝ)*(major1) + (2108238545126737/100000000000000 : ℝ)*(major2) + (9089524901/50000000000000 : ℝ)*(sp1) + (10644658661/50000000000000 : ℝ)*(sp2) + (1400339630891221/50000000000000 : ℝ)*(sp4) + (1400329556244131/50000000000000 : ℝ)*(sp5) + (280065574719249/10000000000000 : ℝ)*(sp6) + (707898750183901/50000000000000 : ℝ)*(sp7) + (707898750183901/50000000000000 : ℝ)*(f.failure) + (1400339630891221/50000000000000 : ℝ)*(f.sum) + (42893892805993/18855000000000000000000000000 : ℝ)*base65 + (30603412373271173/10475000000000000000000000000000 : ℝ)*base68 + (117802392901678827/10475000000000000000000000000000 : ℝ)*base69 + (100768391517928827/10475000000000000000000000000000 : ℝ)*base71 + (97372386893117/18855000000000000000000000000 : ℝ)*base74 + (69838744337628827/10475000000000000000000000000000 : ℝ)*base75 + (25322870912521173/10475000000000000000000000000000 : ℝ)*base78 + (84552474079528827/10475000000000000000000000000000 : ℝ)*base79 + (84589433970973/18855000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8260199/2500000000000000000000 : ℝ)*base89 + (8260199/2500000000000000000000 : ℝ)*base91 + (8260199/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1113_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2057/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8937/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16591/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1113_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8937/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16591/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1113_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1113_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1113_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8937/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16591/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1113_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
