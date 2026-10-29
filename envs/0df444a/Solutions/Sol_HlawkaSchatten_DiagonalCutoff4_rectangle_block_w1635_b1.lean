-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1635_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:01:00.234749+00:00
-- url     : https://prove2.me/submissions/0eef6941-b6db-4988-b217-33bf712a7884

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
theorem support_rectangle_w1635_s3_0 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-328653461/2000000000 : ℝ)*x 0 + (5452145937/10000000000 : ℝ)*x 1 + (323920203/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328653461/2000000000 : ℝ)^4859 ≤ (10145911265693/100000000000000 : ℝ)^3835 := by
    have hnat : (328653461 : ℕ)^4859*100000000000000^3835 ≤ 10145911265693^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328653461 2000000000 10145911265693 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452145937/10000000000 : ℝ)^4859 ≤ (46368944381951/100000000000000 : ℝ)^3835 := by
    have hnat : (5452145937 : ℕ)^4859*100000000000000^3835 ≤ 46368944381951^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452145937 10000000000 46368944381951 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323920203/625000000 : ℝ)^4859 ≤ (10871286082351/25000000000000 : ℝ)^3835 := by
    have hnat : (323920203 : ℕ)^4859*25000000000000^3835 ≤ 10871286082351^3835*625000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323920203 625000000 10871286082351 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-328653461/2000000000 : ℝ), (5452145937/10000000000 : ℝ), (323920203/625000000 : ℝ)] ![(10145911265693/100000000000000 : ℝ), (46368944381951/100000000000000 : ℝ), (10871286082351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-328653461/2000000000 : ℝ)|^4859 ≤ (10145911265693/100000000000000 : ℝ)^3835
        have hw : |(-328653461/2000000000 : ℝ)|=(328653461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452145937/10000000000 : ℝ)|^4859 ≤ (46368944381951/100000000000000 : ℝ)^3835
        have hw : |(5452145937/10000000000 : ℝ)|=(5452145937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323920203/625000000 : ℝ)|^4859 ≤ (10871286082351/25000000000000 : ℝ)^3835
        have hw : |(323920203/625000000 : ℝ)|=(323920203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s3_1 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350021139/10000000000 : ℝ)*x 0 + (-178205227/1000000000 : ℝ)*x 1 + (2591361643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350021139/10000000000 : ℝ)^4859 ≤ (45271253549213/100000000000000 : ℝ)^3835 := by
    have hnat : (5350021139 : ℕ)^4859*100000000000000^3835 ≤ 45271253549213^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350021139 10000000000 45271253549213 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178205227/1000000000 : ℝ)^4859 ≤ (11243601696643/100000000000000 : ℝ)^3835 := by
    have hnat : (178205227 : ℕ)^4859*100000000000000^3835 ≤ 11243601696643^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178205227 1000000000 11243601696643 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591361643/5000000000 : ℝ)^4859 ≤ (43485144733373/100000000000000 : ℝ)^3835 := by
    have hnat : (2591361643 : ℕ)^4859*100000000000000^3835 ≤ 43485144733373^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591361643 5000000000 43485144733373 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350021139/10000000000 : ℝ), (-178205227/1000000000 : ℝ), (2591361643/5000000000 : ℝ)] ![(45271253549213/100000000000000 : ℝ), (11243601696643/100000000000000 : ℝ), (43485144733373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350021139/10000000000 : ℝ)|^4859 ≤ (45271253549213/100000000000000 : ℝ)^3835
        have hw : |(5350021139/10000000000 : ℝ)|=(5350021139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178205227/1000000000 : ℝ)|^4859 ≤ (11243601696643/100000000000000 : ℝ)^3835
        have hw : |(-178205227/1000000000 : ℝ)|=(178205227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591361643/5000000000 : ℝ)|^4859 ≤ (43485144733373/100000000000000 : ℝ)^3835
        have hw : |(2591361643/5000000000 : ℝ)|=(2591361643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s3_2 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350020947/10000000000 : ℝ)*x 0 + (1036544697/2000000000 : ℝ)*x 1 + (-222756533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350020947/10000000000 : ℝ)^4859 ≤ (22635625745359/50000000000000 : ℝ)^3835 := by
    have hnat : (5350020947 : ℕ)^4859*50000000000000^3835 ≤ 22635625745359^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350020947 10000000000 22635625745359 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036544697/2000000000 : ℝ)^4859 ≤ (8697029369779/20000000000000 : ℝ)^3835 := by
    have hnat : (1036544697 : ℕ)^4859*20000000000000^3835 ≤ 8697029369779^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036544697 2000000000 8697029369779 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222756533/1250000000 : ℝ)^4859 ≤ (11243601648679/100000000000000 : ℝ)^3835 := by
    have hnat : (222756533 : ℕ)^4859*100000000000000^3835 ≤ 11243601648679^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222756533 1250000000 11243601648679 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350020947/10000000000 : ℝ), (1036544697/2000000000 : ℝ), (-222756533/1250000000 : ℝ)] ![(22635625745359/50000000000000 : ℝ), (8697029369779/20000000000000 : ℝ), (11243601648679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350020947/10000000000 : ℝ)|^4859 ≤ (22635625745359/50000000000000 : ℝ)^3835
        have hw : |(5350020947/10000000000 : ℝ)|=(5350020947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036544697/2000000000 : ℝ)|^4859 ≤ (8697029369779/20000000000000 : ℝ)^3835
        have hw : |(1036544697/2000000000 : ℝ)|=(1036544697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222756533/1250000000 : ℝ)|^4859 ≤ (11243601648679/100000000000000 : ℝ)^3835
        have hw : |(-222756533/1250000000 : ℝ)|=(222756533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s3_3 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2096181/5000000 : ℝ)*x 0 + (3860748869/10000000000 : ℝ)*x 1 + (1136164307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096181/5000000 : ℝ)^4859 ≤ (4154893224603/12500000000000 : ℝ)^3835 := by
    have hnat : (2096181 : ℕ)^4859*12500000000000^3835 ≤ 4154893224603^3835*5000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096181 5000000 4154893224603 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3860748869/10000000000 : ℝ)^4859 ≤ (29943801126699/100000000000000 : ℝ)^3835 := by
    have hnat : (3860748869 : ℕ)^4859*100000000000000^3835 ≤ 29943801126699^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3860748869 10000000000 29943801126699 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136164307/2500000000 : ℝ)^4859 ≤ (920426326673/2500000000000 : ℝ)^3835 := by
    have hnat : (1136164307 : ℕ)^4859*2500000000000^3835 ≤ 920426326673^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136164307 2500000000 920426326673 2500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096181/5000000 : ℝ), (3860748869/10000000000 : ℝ), (1136164307/2500000000 : ℝ)] ![(4154893224603/12500000000000 : ℝ), (29943801126699/100000000000000 : ℝ), (920426326673/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096181/5000000 : ℝ)|^4859 ≤ (4154893224603/12500000000000 : ℝ)^3835
        have hw : |(2096181/5000000 : ℝ)|=(2096181/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3860748869/10000000000 : ℝ)|^4859 ≤ (29943801126699/100000000000000 : ℝ)^3835
        have hw : |(3860748869/10000000000 : ℝ)|=(3860748869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136164307/2500000000 : ℝ)|^4859 ≤ (920426326673/2500000000000 : ℝ)^3835
        have hw : |(1136164307/2500000000 : ℝ)|=(1136164307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s3_4 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-410833551/2500000000 : ℝ)*x 0 + (2592375697/5000000000 : ℝ)*x 1 + (1362524069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410833551/2500000000 : ℝ)^4859 ≤ (634152163039/6250000000000 : ℝ)^3835 := by
    have hnat : (410833551 : ℕ)^4859*6250000000000^3835 ≤ 634152163039^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410833551 2500000000 634152163039 6250000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592375697/5000000000 : ℝ)^4859 ≤ (43506706194791/100000000000000 : ℝ)^3835 := by
    have hnat : (2592375697 : ℕ)^4859*100000000000000^3835 ≤ 43506706194791^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592375697 5000000000 43506706194791 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362524069/2500000000 : ℝ)^4859 ≤ (11586714793339/25000000000000 : ℝ)^3835 := by
    have hnat : (1362524069 : ℕ)^4859*25000000000000^3835 ≤ 11586714793339^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362524069 2500000000 11586714793339 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410833551/2500000000 : ℝ), (2592375697/5000000000 : ℝ), (1362524069/2500000000 : ℝ)] ![(634152163039/6250000000000 : ℝ), (43506706194791/100000000000000 : ℝ), (11586714793339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410833551/2500000000 : ℝ)|^4859 ≤ (634152163039/6250000000000 : ℝ)^3835
        have hw : |(-410833551/2500000000 : ℝ)|=(410833551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592375697/5000000000 : ℝ)|^4859 ≤ (43506706194791/100000000000000 : ℝ)^3835
        have hw : |(2592375697/5000000000 : ℝ)|=(2592375697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362524069/2500000000 : ℝ)|^4859 ≤ (11586714793339/25000000000000 : ℝ)^3835
        have hw : |(1362524069/2500000000 : ℝ)|=(1362524069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s3_5 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278182623/10000000000 : ℝ)*x 0 + (-1514679381/10000000000 : ℝ)*x 1 + (2725048161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278182623/10000000000 : ℝ)^4859 ≤ (44502434606771/100000000000000 : ℝ)^3835 := by
    have hnat : (5278182623 : ℕ)^4859*100000000000000^3835 ≤ 44502434606771^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278182623 10000000000 44502434606771 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514679381/10000000000 : ℝ)^4859 ≤ (9150705709809/100000000000000 : ℝ)^3835 := by
    have hnat : (1514679381 : ℕ)^4859*100000000000000^3835 ≤ 9150705709809^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514679381 10000000000 9150705709809 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725048161/5000000000 : ℝ)^4859 ≤ (5793357458623/12500000000000 : ℝ)^3835 := by
    have hnat : (2725048161 : ℕ)^4859*12500000000000^3835 ≤ 5793357458623^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725048161 5000000000 5793357458623 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278182623/10000000000 : ℝ), (-1514679381/10000000000 : ℝ), (2725048161/5000000000 : ℝ)] ![(44502434606771/100000000000000 : ℝ), (9150705709809/100000000000000 : ℝ), (5793357458623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278182623/10000000000 : ℝ)|^4859 ≤ (44502434606771/100000000000000 : ℝ)^3835
        have hw : |(5278182623/10000000000 : ℝ)|=(5278182623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1514679381/10000000000 : ℝ)|^4859 ≤ (9150705709809/100000000000000 : ℝ)^3835
        have hw : |(-1514679381/10000000000 : ℝ)|=(1514679381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725048161/5000000000 : ℝ)|^4859 ≤ (5793357458623/12500000000000 : ℝ)^3835
        have hw : |(2725048161/5000000000 : ℝ)|=(2725048161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s3_6 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319545673/2500000000 : ℝ)*x 0 + (2725048177/5000000000 : ℝ)*x 1 + (-37866981/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319545673/2500000000 : ℝ)^4859 ≤ (44502435343877/100000000000000 : ℝ)^3835 := by
    have hnat : (1319545673 : ℕ)^4859*100000000000000^3835 ≤ 44502435343877^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319545673 2500000000 44502435343877 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725048177/5000000000 : ℝ)^4859 ≤ (5793357501721/12500000000000 : ℝ)^3835 := by
    have hnat : (2725048177 : ℕ)^4859*12500000000000^3835 ≤ 5793357501721^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725048177 5000000000 5793357501721 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37866981/250000000 : ℝ)^4859 ≤ (35744939963/390625000000 : ℝ)^3835 := by
    have hnat : (37866981 : ℕ)^4859*390625000000^3835 ≤ 35744939963^3835*250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37866981 250000000 35744939963 390625000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319545673/2500000000 : ℝ), (2725048177/5000000000 : ℝ), (-37866981/250000000 : ℝ)] ![(44502435343877/100000000000000 : ℝ), (5793357501721/12500000000000 : ℝ), (35744939963/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319545673/2500000000 : ℝ)|^4859 ≤ (44502435343877/100000000000000 : ℝ)^3835
        have hw : |(1319545673/2500000000 : ℝ)|=(1319545673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725048177/5000000000 : ℝ)|^4859 ≤ (5793357501721/12500000000000 : ℝ)^3835
        have hw : |(2725048177/5000000000 : ℝ)|=(2725048177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37866981/250000000 : ℝ)|^4859 ≤ (35744939963/390625000000 : ℝ)^3835
        have hw : |(-37866981/250000000 : ℝ)|=(37866981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s3_7 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262033231/625000000 : ℝ)*x 0 + (2269754573/5000000000 : ℝ)*x 1 + (3865950869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262033231/625000000 : ℝ)^4859 ≤ (33240850491331/100000000000000 : ℝ)^3835 := by
    have hnat : (262033231 : ℕ)^4859*100000000000000^3835 ≤ 33240850491331^3835*625000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262033231 625000000 33240850491331 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269754573/5000000000 : ℝ)^4859 ≤ (2297763724513/6250000000000 : ℝ)^3835 := by
    have hnat : (2269754573 : ℕ)^4859*6250000000000^3835 ≤ 2297763724513^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269754573 5000000000 2297763724513 6250000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3865950869/10000000000 : ℝ)^4859 ≤ (5998985979393/20000000000000 : ℝ)^3835 := by
    have hnat : (3865950869 : ℕ)^4859*20000000000000^3835 ≤ 5998985979393^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865950869 10000000000 5998985979393 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262033231/625000000 : ℝ), (2269754573/5000000000 : ℝ), (3865950869/10000000000 : ℝ)] ![(33240850491331/100000000000000 : ℝ), (2297763724513/6250000000000 : ℝ), (5998985979393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262033231/625000000 : ℝ)|^4859 ≤ (33240850491331/100000000000000 : ℝ)^3835
        have hw : |(262033231/625000000 : ℝ)|=(262033231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2269754573/5000000000 : ℝ)|^4859 ≤ (2297763724513/6250000000000 : ℝ)^3835
        have hw : |(2269754573/5000000000 : ℝ)|=(2269754573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3865950869/10000000000 : ℝ)|^4859 ≤ (5998985979393/20000000000000 : ℝ)^3835
        have hw : |(3865950869/10000000000 : ℝ)|=(3865950869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1635_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5291/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1019/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16397/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16397/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16397/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16397/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16397/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16397/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10499/100000 : ℝ) ^ (4855/1024 : ℝ) ≤ (2285892941743301/100000000000000000000 : ℝ) := by
    have hpowers : (10499/100000 : ℝ)^4855 ≤ (2285892941743301/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10499 : ℕ)^4855*100000000000000000000^1024 ≤ 2285892941743301^1024*100000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10499 100000 2285892941743301 100000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10499/100000 : ℝ)) (X := (2285892941743301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16397/100000 : ℝ) ^ (4855/1024 : ℝ) ≤ (18924846646298853/100000000000000000000 : ℝ) := by
    have hpowers : (16397/100000 : ℝ)^4855 ≤ (18924846646298853/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16397 : ℕ)^4855*100000000000000000000^1024 ≤ 18924846646298853^1024*100000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16397 100000 18924846646298853 100000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16397/100000 : ℝ)) (X := (18924846646298853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002285892941743301/50000000000000000000 : ℝ) ≤ (5000048212402717/5000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (50002285892941743301/50000000000000000000 : ℝ)^1024 ≤ (5000048212402717/5000000000000000 : ℝ)^4855 := by
      have hnat : (50002285892941743301 : ℕ)^1024*5000000000000000^4855 ≤ 5000048212402717^4855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002285892941743301 50000000000000000000 5000048212402717 5000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000048212402717/5000000000000000 : ℝ)) (X := (50002285892941743301/50000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010605369794021077/50000000000000000000 : ℝ) ≤ (5000223666116809/5000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (50010605369794021077/50000000000000000000 : ℝ)^1024 ≤ (5000223666116809/5000000000000000 : ℝ)^4855 := by
      have hnat : (50010605369794021077 : ℕ)^1024*5000000000000000^4855 ≤ 5000223666116809^4855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010605369794021077 50000000000000000000 5000223666116809 5000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000223666116809/5000000000000000 : ℝ)) (X := (50010605369794021077/50000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018924846646298853/50000000000000000000 : ℝ) ≤ (5000399119830901/5000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (50018924846646298853/50000000000000000000 : ℝ)^1024 ≤ (5000399119830901/5000000000000000 : ℝ)^4855 := by
      have hnat : (50018924846646298853 : ℕ)^1024*5000000000000000^4855 ≤ 5000399119830901^4855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018924846646298853 50000000000000000000 5000399119830901 5000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000399119830901/5000000000000000 : ℝ)) (X := (50018924846646298853/50000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2285892941743301/100000000000000000000 : ℝ) ≤ ((196577334531084807/196600000000000000 : ℝ)+2*(14621142841/24575000000000 : ℝ)*(10499/100000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (196577334531084807/196600000000000000 : ℝ)+2*(14621142841/24575000000000 : ℝ)*(10499/100000 : ℝ)=(5000048212402717/5000000000000000 : ℝ) by norm_num, show 1+2*(2285892941743301/100000000000000000000 : ℝ)=(50002285892941743301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18924846646298853/100000000000000000000 : ℝ)+(2285892941743301/100000000000000000000 : ℝ) ≤ ((196577334531084807/196600000000000000 : ℝ)+(14621142841/24575000000000 : ℝ)*((16397/100000 : ℝ)+(10499/100000 : ℝ)))^(4855/1024 : ℝ) := by
    rw [show (196577334531084807/196600000000000000 : ℝ)+(14621142841/24575000000000 : ℝ)*((16397/100000 : ℝ)+(10499/100000 : ℝ))=(5000223666116809/5000000000000000 : ℝ) by norm_num, show 1+(18924846646298853/100000000000000000000 : ℝ)+(2285892941743301/100000000000000000000 : ℝ)=(50010605369794021077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18924846646298853/100000000000000000000 : ℝ) ≤ ((196577334531084807/196600000000000000 : ℝ)+2*(14621142841/24575000000000 : ℝ)*(16397/100000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (196577334531084807/196600000000000000 : ℝ)+2*(14621142841/24575000000000 : ℝ)*(16397/100000 : ℝ)=(5000399119830901/5000000000000000 : ℝ) by norm_num, show 1+2*(18924846646298853/100000000000000000000 : ℝ)=(50018924846646298853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (196577334531084807/196600000000000000 : ℝ)*(X 1 0+X 2 0)+(14621142841/24575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (10499/100000 : ℝ)) (hi := (16397/100000 : ℝ)) (c := (196577334531084807/196600000000000000 : ℝ)) (alpha := (14621142841/24575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (196577334531084807/196600000000000000 : ℝ)*(X 0 1+X 2 1)+(14621142841/24575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (10499/100000 : ℝ)) (hi := (16397/100000 : ℝ)) (c := (196577334531084807/196600000000000000 : ℝ)) (alpha := (14621142841/24575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (196577334531084807/196600000000000000 : ℝ)*(X 0 2+X 1 2)+(14621142841/24575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (10499/100000 : ℝ)) (hi := (16397/100000 : ℝ)) (c := (196577334531084807/196600000000000000 : ℝ)) (alpha := (14621142841/24575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-328653461/2000000000 : ℝ)*X 0 0+(5452145937/10000000000 : ℝ)*X 0 1+(323920203/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350021139/10000000000 : ℝ)*X 1 0+(-178205227/1000000000 : ℝ)*X 1 1+(2591361643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350020947/10000000000 : ℝ)*X 2 0+(1036544697/2000000000 : ℝ)*X 2 1+(-222756533/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2096181/5000000 : ℝ)*X 0 0+(3860748869/10000000000 : ℝ)*X 0 1+(1136164307/2500000000 : ℝ)*X 0 2+(2096181/5000000 : ℝ)*X 1 0+(3860748869/10000000000 : ℝ)*X 1 1+(1136164307/2500000000 : ℝ)*X 1 2+(2096181/5000000 : ℝ)*X 2 0+(3860748869/10000000000 : ℝ)*X 2 1+(1136164307/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-410833551/2500000000 : ℝ)*X 0 0+(2592375697/5000000000 : ℝ)*X 0 1+(1362524069/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278182623/10000000000 : ℝ)*X 1 0+(-1514679381/10000000000 : ℝ)*X 1 1+(2725048161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319545673/2500000000 : ℝ)*X 2 0+(2725048177/5000000000 : ℝ)*X 2 1+(-37866981/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((262033231/625000000 : ℝ)*X 0 0+(2269754573/5000000000 : ℝ)*X 0 1+(3865950869/10000000000 : ℝ)*X 0 2+(262033231/625000000 : ℝ)*X 1 0+(2269754573/5000000000 : ℝ)*X 1 1+(3865950869/10000000000 : ℝ)*X 1 2+(262033231/625000000 : ℝ)*X 2 0+(2269754573/5000000000 : ℝ)*X 2 1+(3865950869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54542519438089757885146803/4915000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (818381943/50000000000000 : ℝ)*(base19) + (1354086393/100000000000000 : ℝ)*(base23) + (2559/3200000000 : ℝ)*(lower2) + (59609767/25000000000000 : ℝ)*(upper3) + (58179401/50000000000000 : ℝ)*(upper5) + (1293471123824419/50000000000000 : ℝ)*(major0) + (1293471123824419/50000000000000 : ℝ)*(major1) + (1293471123824419/50000000000000 : ℝ)*(major2) + (1855831444650699/50000000000000 : ℝ)*(sp0) + (3711682351890419/100000000000000 : ℝ)*(sp1) + (3711682634567913/100000000000000 : ℝ)*(sp2) + (1462191565350449/100000000000000 : ℝ)*(sp3) + (21099352907/100000000000000 : ℝ)*(sp4) + (2142846931/25000000000000 : ℝ)*(sp7) + (1462200136738173/100000000000000 : ℝ)*(f.failure) + (1855841994327153/50000000000000 : ℝ)*(f.sum) + (7933297988171/2457500000000000000000000000 : ℝ)*base65 + (176008162140264133/9830000000000000000000000000000 : ℝ)*base67 + (9901172137414133/9830000000000000000000000000000 : ℝ)*base69 + (72142740766184133/9830000000000000000000000000000 : ℝ)*base71 + (26072100654207/4915000000000000000000000000 : ℝ)*base73 + (104980649863074133/9830000000000000000000000000000 : ℝ)*base75 + (46756703149084133/9830000000000000000000000000000 : ℝ)*base77 + (71886693398834133/9830000000000000000000000000000 : ℝ)*base79 + (369429486601/614375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (19191961/2000000000000000000000 : ℝ)*base90 + (19191961/2000000000000000000000 : ℝ)*base92 + (19191961/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6346353447201380780605053/491500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (949310907/50000000000000 : ℝ)*(base19) + (85950947/4000000000000 : ℝ)*(base23) + (151655757/50000000000000 : ℝ)*(upper3) + (72084143/100000000000000 : ℝ)*(lower4) + (62862357/25000000000000 : ℝ)*(upper5) + (262666572898993/10000000000000 : ℝ)*(major0) + (262666572898993/10000000000000 : ℝ)*(major1) + (262666572898993/10000000000000 : ℝ)*(major2) + (21613213173/100000000000000 : ℝ)*(sp1) + (26338728397/100000000000000 : ℝ)*(sp2) + (3768678252047769/100000000000000 : ℝ)*(sp4) + (3768654740212783/100000000000000 : ℝ)*(sp5) + (1884324882272849/50000000000000 : ℝ)*(sp6) + (1484652775524931/100000000000000 : ℝ)*(sp7) + (1484652775524931/100000000000000 : ℝ)*(f.failure) + (3768678252047769/100000000000000 : ℝ)*(f.sum) + (1088025887849/245750000000000000000000000 : ℝ)*base66 + (4148401779811351/1966000000000000000000000000000 : ℝ)*base67 + (6426052373574649/1966000000000000000000000000000 : ℝ)*base70 + (16838624470908649/1966000000000000000000000000000 : ℝ)*base72 + (327243528217/196600000000000000000000000 : ℝ)*base73 + (37712430533334649/1966000000000000000000000000000 : ℝ)*base76 + (20582000766862649/1966000000000000000000000000000 : ℝ)*base78 + (18710572468054649/1966000000000000000000000000000 : ℝ)*base80 + (1371296238009/983000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11062233/2000000000000000000000 : ℝ)*base89 + (11062233/2000000000000000000000 : ℝ)*base91 + (11062233/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1635_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5291/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1635_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1635_s4_0 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-410833081/2500000000 : ℝ)*x 0 + (1090364251/2000000000 : ℝ)*x 1 + (647875563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410833081/2500000000 : ℝ)^4859 ≤ (1014641990153/10000000000000 : ℝ)^3835 := by
    have hnat : (410833081 : ℕ)^4859*10000000000000^3835 ≤ 1014641990153^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410833081 2500000000 1014641990153 10000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090364251/2000000000 : ℝ)^4859 ≤ (4636544576797/10000000000000 : ℝ)^3835 := by
    have hnat : (1090364251 : ℕ)^4859*10000000000000^3835 ≤ 4636544576797^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090364251 2000000000 4636544576797 10000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647875563/1250000000 : ℝ)^4859 ≤ (43488134316889/100000000000000 : ℝ)^3835 := by
    have hnat : (647875563 : ℕ)^4859*100000000000000^3835 ≤ 43488134316889^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647875563 1250000000 43488134316889 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410833081/2500000000 : ℝ), (1090364251/2000000000 : ℝ), (647875563/1250000000 : ℝ)] ![(1014641990153/10000000000000 : ℝ), (4636544576797/10000000000000 : ℝ), (43488134316889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410833081/2500000000 : ℝ)|^4859 ≤ (1014641990153/10000000000000 : ℝ)^3835
        have hw : |(-410833081/2500000000 : ℝ)|=(410833081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090364251/2000000000 : ℝ)|^4859 ≤ (4636544576797/10000000000000 : ℝ)^3835
        have hw : |(1090364251/2000000000 : ℝ)|=(1090364251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647875563/1250000000 : ℝ)|^4859 ≤ (43488134316889/100000000000000 : ℝ)^3835
        have hw : |(647875563/1250000000 : ℝ)|=(647875563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s4_1 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267496667/500000000 : ℝ)*x 0 + (-89089803/500000000 : ℝ)*x 1 + (518300449/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267496667/500000000 : ℝ)^4859 ≤ (45270312229463/100000000000000 : ℝ)^3835 := by
    have hnat : (267496667 : ℕ)^4859*100000000000000^3835 ≤ 45270312229463^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267496667 500000000 45270312229463 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89089803/500000000 : ℝ)^4859 ≤ (2248310716379/20000000000000 : ℝ)^3835 := by
    have hnat : (89089803 : ℕ)^4859*20000000000000^3835 ≤ 2248310716379^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89089803 500000000 2248310716379 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518300449/1000000000 : ℝ)^4859 ≤ (5436016771007/12500000000000 : ℝ)^3835 := by
    have hnat : (518300449 : ℕ)^4859*12500000000000^3835 ≤ 5436016771007^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518300449 1000000000 5436016771007 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267496667/500000000 : ℝ), (-89089803/500000000 : ℝ), (518300449/1000000000 : ℝ)] ![(45270312229463/100000000000000 : ℝ), (2248310716379/20000000000000 : ℝ), (5436016771007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267496667/500000000 : ℝ)|^4859 ≤ (45270312229463/100000000000000 : ℝ)^3835
        have hw : |(267496667/500000000 : ℝ)|=(267496667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89089803/500000000 : ℝ)|^4859 ≤ (2248310716379/20000000000000 : ℝ)^3835
        have hw : |(-89089803/500000000 : ℝ)|=(89089803/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518300449/1000000000 : ℝ)|^4859 ≤ (5436016771007/12500000000000 : ℝ)^3835
        have hw : |(518300449/1000000000 : ℝ)|=(518300449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s4_2 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674966667/5000000000 : ℝ)*x 0 + (5183004499/10000000000 : ℝ)*x 1 + (-890898029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674966667/5000000000 : ℝ)^4859 ≤ (9054062433027/20000000000000 : ℝ)^3835 := by
    have hnat : (2674966667 : ℕ)^4859*20000000000000^3835 ≤ 9054062433027^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674966667 5000000000 9054062433027 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183004499/10000000000 : ℝ)^4859 ≤ (21744067131867/50000000000000 : ℝ)^3835 := by
    have hnat : (5183004499 : ℕ)^4859*50000000000000^3835 ≤ 21744067131867^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183004499 10000000000 21744067131867 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890898029/5000000000 : ℝ)^4859 ≤ (2810388391477/25000000000000 : ℝ)^3835 := by
    have hnat : (890898029 : ℕ)^4859*25000000000000^3835 ≤ 2810388391477^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890898029 5000000000 2810388391477 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674966667/5000000000 : ℝ), (5183004499/10000000000 : ℝ), (-890898029/5000000000 : ℝ)] ![(9054062433027/20000000000000 : ℝ), (21744067131867/50000000000000 : ℝ), (2810388391477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674966667/5000000000 : ℝ)|^4859 ≤ (9054062433027/20000000000000 : ℝ)^3835
        have hw : |(2674966667/5000000000 : ℝ)|=(2674966667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183004499/10000000000 : ℝ)|^4859 ≤ (21744067131867/50000000000000 : ℝ)^3835
        have hw : |(5183004499/10000000000 : ℝ)|=(5183004499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890898029/5000000000 : ℝ)|^4859 ≤ (2810388391477/25000000000000 : ℝ)^3835
        have hw : |(-890898029/5000000000 : ℝ)|=(890898029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s4_3 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209620219/500000000 : ℝ)*x 0 + (482689133/1250000000 : ℝ)*x 1 + (4543884083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209620219/500000000 : ℝ)^4859 ≤ (103873661021/312500000000 : ℝ)^3835 := by
    have hnat : (209620219 : ℕ)^4859*312500000000^3835 ≤ 103873661021^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209620219 500000000 103873661021 312500000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482689133/1250000000 : ℝ)^4859 ≤ (7487827749851/25000000000000 : ℝ)^3835 := by
    have hnat : (482689133 : ℕ)^4859*25000000000000^3835 ≤ 7487827749851^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482689133 1250000000 7487827749851 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4543884083/10000000000 : ℝ)^4859 ≤ (36809117453403/100000000000000 : ℝ)^3835 := by
    have hnat : (4543884083 : ℕ)^4859*100000000000000^3835 ≤ 36809117453403^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543884083 10000000000 36809117453403 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209620219/500000000 : ℝ), (482689133/1250000000 : ℝ), (4543884083/10000000000 : ℝ)] ![(103873661021/312500000000 : ℝ), (7487827749851/25000000000000 : ℝ), (36809117453403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209620219/500000000 : ℝ)|^4859 ≤ (103873661021/312500000000 : ℝ)^3835
        have hw : |(209620219/500000000 : ℝ)|=(209620219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482689133/1250000000 : ℝ)|^4859 ≤ (7487827749851/25000000000000 : ℝ)^3835
        have hw : |(482689133/1250000000 : ℝ)|=(482689133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4543884083/10000000000 : ℝ)|^4859 ≤ (36809117453403/100000000000000 : ℝ)^3835
        have hw : |(4543884083/10000000000 : ℝ)|=(4543884083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s4_4 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-164339859/1000000000 : ℝ)*x 0 + (64812793/125000000 : ℝ)*x 1 + (136244527/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164339859/1000000000 : ℝ)^4859 ≤ (10146938298027/100000000000000 : ℝ)^3835 := by
    have hnat : (164339859 : ℕ)^4859*100000000000000^3835 ≤ 10146938298027^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164339859 1000000000 10146938298027 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64812793/125000000 : ℝ)^4859 ≤ (21754799286849/50000000000000 : ℝ)^3835 := by
    have hnat : (64812793 : ℕ)^4859*50000000000000^3835 ≤ 21754799286849^3835*125000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64812793 125000000 21754799286849 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136244527/250000000 : ℝ)^4859 ≤ (23171731558029/50000000000000 : ℝ)^3835 := by
    have hnat : (136244527 : ℕ)^4859*50000000000000^3835 ≤ 23171731558029^3835*250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136244527 250000000 23171731558029 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-164339859/1000000000 : ℝ), (64812793/125000000 : ℝ), (136244527/250000000 : ℝ)] ![(10146938298027/100000000000000 : ℝ), (21754799286849/50000000000000 : ℝ), (23171731558029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-164339859/1000000000 : ℝ)|^4859 ≤ (10146938298027/100000000000000 : ℝ)^3835
        have hw : |(-164339859/1000000000 : ℝ)|=(164339859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64812793/125000000 : ℝ)|^4859 ≤ (21754799286849/50000000000000 : ℝ)^3835
        have hw : |(64812793/125000000 : ℝ)|=(64812793/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136244527/250000000 : ℝ)|^4859 ≤ (23171731558029/50000000000000 : ℝ)^3835
        have hw : |(136244527/250000000 : ℝ)|=(136244527/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s4_5 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639128437/5000000000 : ℝ)*x 0 + (-378754869/2500000000 : ℝ)*x 1 + (2724890541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639128437/5000000000 : ℝ)^4859 ≤ (44503227809157/100000000000000 : ℝ)^3835 := by
    have hnat : (2639128437 : ℕ)^4859*100000000000000^3835 ≤ 44503227809157^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639128437 5000000000 44503227809157 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378754869/2500000000 : ℝ)^4859 ≤ (9153309036497/100000000000000 : ℝ)^3835 := by
    have hnat : (378754869 : ℕ)^4859*100000000000000^3835 ≤ 9153309036497^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378754869 2500000000 9153309036497 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724890541/5000000000 : ℝ)^4859 ≤ (46343463137607/100000000000000 : ℝ)^3835 := by
    have hnat : (2724890541 : ℕ)^4859*100000000000000^3835 ≤ 46343463137607^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724890541 5000000000 46343463137607 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639128437/5000000000 : ℝ), (-378754869/2500000000 : ℝ), (2724890541/5000000000 : ℝ)] ![(44503227809157/100000000000000 : ℝ), (9153309036497/100000000000000 : ℝ), (46343463137607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639128437/5000000000 : ℝ)|^4859 ≤ (44503227809157/100000000000000 : ℝ)^3835
        have hw : |(2639128437/5000000000 : ℝ)|=(2639128437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378754869/2500000000 : ℝ)|^4859 ≤ (9153309036497/100000000000000 : ℝ)^3835
        have hw : |(-378754869/2500000000 : ℝ)|=(378754869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724890541/5000000000 : ℝ)|^4859 ≤ (46343463137607/100000000000000 : ℝ)^3835
        have hw : |(2724890541/5000000000 : ℝ)|=(2724890541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s4_6 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278256879/10000000000 : ℝ)*x 0 + (1362445269/2500000000 : ℝ)*x 1 + (-1515019477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278256879/10000000000 : ℝ)^4859 ≤ (4450322786257/10000000000000 : ℝ)^3835 := by
    have hnat : (5278256879 : ℕ)^4859*10000000000000^3835 ≤ 4450322786257^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278256879 10000000000 4450322786257 10000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362445269/2500000000 : ℝ)^4859 ≤ (46343463072961/100000000000000 : ℝ)^3835 := by
    have hnat : (1362445269 : ℕ)^4859*100000000000000^3835 ≤ 46343463072961^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362445269 2500000000 46343463072961 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1515019477/10000000000 : ℝ)^4859 ≤ (1144163630519/12500000000000 : ℝ)^3835 := by
    have hnat : (1515019477 : ℕ)^4859*12500000000000^3835 ≤ 1144163630519^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515019477 10000000000 1144163630519 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278256879/10000000000 : ℝ), (1362445269/2500000000 : ℝ), (-1515019477/10000000000 : ℝ)] ![(4450322786257/10000000000000 : ℝ), (46343463072961/100000000000000 : ℝ), (1144163630519/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278256879/10000000000 : ℝ)|^4859 ≤ (4450322786257/10000000000000 : ℝ)^3835
        have hw : |(5278256879/10000000000 : ℝ)|=(5278256879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362445269/2500000000 : ℝ)|^4859 ≤ (46343463072961/100000000000000 : ℝ)^3835
        have hw : |(1362445269/2500000000 : ℝ)|=(1362445269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1515019477/10000000000 : ℝ)|^4859 ≤ (1144163630519/12500000000000 : ℝ)^3835
        have hw : |(-1515019477/10000000000 : ℝ)|=(1515019477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s4_7 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2096286311/5000000000 : ℝ)*x 0 + (2269379577/5000000000 : ℝ)*x 1 + (1933345933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096286311/5000000000 : ℝ)^4859 ≤ (33241261619439/100000000000000 : ℝ)^3835 := by
    have hnat : (2096286311 : ℕ)^4859*100000000000000^3835 ≤ 33241261619439^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096286311 5000000000 33241261619439 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269379577/5000000000 : ℝ)^4859 ≤ (36756523946989/100000000000000 : ℝ)^3835 := by
    have hnat : (2269379577 : ℕ)^4859*100000000000000^3835 ≤ 36756523946989^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269379577 5000000000 36756523946989 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1933345933/5000000000 : ℝ)^4859 ≤ (15001107205749/50000000000000 : ℝ)^3835 := by
    have hnat : (1933345933 : ℕ)^4859*50000000000000^3835 ≤ 15001107205749^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933345933 5000000000 15001107205749 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096286311/5000000000 : ℝ), (2269379577/5000000000 : ℝ), (1933345933/5000000000 : ℝ)] ![(33241261619439/100000000000000 : ℝ), (36756523946989/100000000000000 : ℝ), (15001107205749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096286311/5000000000 : ℝ)|^4859 ≤ (33241261619439/100000000000000 : ℝ)^3835
        have hw : |(2096286311/5000000000 : ℝ)|=(2096286311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2269379577/5000000000 : ℝ)|^4859 ≤ (36756523946989/100000000000000 : ℝ)^3835
        have hw : |(2269379577/5000000000 : ℝ)|=(2269379577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1933345933/5000000000 : ℝ)|^4859 ≤ (15001107205749/50000000000000 : ℝ)^3835
        have hw : |(1933345933/5000000000 : ℝ)|=(1933345933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1635_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5291/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2647/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16297/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5291/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5291/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5291/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5291/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5291/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5291/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5291/50000 : ℝ) ^ (4855/1024 : ℝ) ≤ (148303021367819/6250000000000000000 : ℝ) := by
    have hpowers : (5291/50000 : ℝ)^4855 ≤ (148303021367819/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5291 : ℕ)^4855*6250000000000000000^1024 ≤ 148303021367819^1024*50000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5291 50000 148303021367819 6250000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5291/50000 : ℝ)) (X := (148303021367819/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1019/6250 : ℝ) ^ (4855/1024 : ℝ) ≤ (1842130899801711/10000000000000000000 : ℝ) := by
    have hpowers : (1019/6250 : ℝ)^4855 ≤ (1842130899801711/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1019 : ℕ)^4855*10000000000000000000^1024 ≤ 1842130899801711^1024*6250^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1019 6250 1842130899801711 10000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1019/6250 : ℝ)) (X := (1842130899801711/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125148303021367819/3125000000000000000 : ℝ) ≤ (10000100092737733/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (3125148303021367819/3125000000000000000 : ℝ)^1024 ≤ (10000100092737733/10000000000000000 : ℝ)^4855 := by
      have hnat : (3125148303021367819 : ℕ)^1024*10000000000000000^4855 ≤ 10000100092737733^4855*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125148303021367819 3125000000000000000 10000100092737733 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000100092737733/10000000000000000 : ℝ)) (X := (3125148303021367819/3125000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010397078669951107/50000000000000000000 : ℝ) ≤ (10000438547279147/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (50010397078669951107/50000000000000000000 : ℝ)^1024 ≤ (10000438547279147/10000000000000000 : ℝ)^4855 := by
      have hnat : (50010397078669951107 : ℕ)^1024*10000000000000000^4855 ≤ 10000438547279147^4855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010397078669951107 50000000000000000000 10000438547279147 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000438547279147/10000000000000000 : ℝ)) (X := (50010397078669951107/50000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001842130899801711/5000000000000000000 : ℝ) ≤ (10000777001820561/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (5001842130899801711/5000000000000000000 : ℝ)^1024 ≤ (10000777001820561/10000000000000000 : ℝ)^4855 := by
      have hnat : (5001842130899801711 : ℕ)^1024*10000000000000000^4855 ≤ 10000777001820561^4855*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001842130899801711 5000000000000000000 10000777001820561 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000777001820561/10000000000000000 : ℝ)) (X := (5001842130899801711/5000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(148303021367819/6250000000000000000 : ℝ) ≤ ((5721340967873082233/5722000000000000000 : ℝ)+2*(169227270707/286100000000000 : ℝ)*(5291/50000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (5721340967873082233/5722000000000000000 : ℝ)+2*(169227270707/286100000000000 : ℝ)*(5291/50000 : ℝ)=(10000100092737733/10000000000000000 : ℝ) by norm_num, show 1+2*(148303021367819/6250000000000000000 : ℝ)=(3125148303021367819/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1842130899801711/10000000000000000000 : ℝ)+(148303021367819/6250000000000000000 : ℝ) ≤ ((5721340967873082233/5722000000000000000 : ℝ)+(169227270707/286100000000000 : ℝ)*((1019/6250 : ℝ)+(5291/50000 : ℝ)))^(4855/1024 : ℝ) := by
    rw [show (5721340967873082233/5722000000000000000 : ℝ)+(169227270707/286100000000000 : ℝ)*((1019/6250 : ℝ)+(5291/50000 : ℝ))=(10000438547279147/10000000000000000 : ℝ) by norm_num, show 1+(1842130899801711/10000000000000000000 : ℝ)+(148303021367819/6250000000000000000 : ℝ)=(50010397078669951107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1842130899801711/10000000000000000000 : ℝ) ≤ ((5721340967873082233/5722000000000000000 : ℝ)+2*(169227270707/286100000000000 : ℝ)*(1019/6250 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (5721340967873082233/5722000000000000000 : ℝ)+2*(169227270707/286100000000000 : ℝ)*(1019/6250 : ℝ)=(10000777001820561/10000000000000000 : ℝ) by norm_num, show 1+2*(1842130899801711/10000000000000000000 : ℝ)=(5001842130899801711/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5721340967873082233/5722000000000000000 : ℝ)*(X 1 0+X 2 0)+(169227270707/286100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (5291/50000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (5721340967873082233/5722000000000000000 : ℝ)) (alpha := (169227270707/286100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5721340967873082233/5722000000000000000 : ℝ)*(X 0 1+X 2 1)+(169227270707/286100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (5291/50000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (5721340967873082233/5722000000000000000 : ℝ)) (alpha := (169227270707/286100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5721340967873082233/5722000000000000000 : ℝ)*(X 0 2+X 1 2)+(169227270707/286100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (5291/50000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (5721340967873082233/5722000000000000000 : ℝ)) (alpha := (169227270707/286100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-410833081/2500000000 : ℝ)*X 0 0+(1090364251/2000000000 : ℝ)*X 0 1+(647875563/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267496667/500000000 : ℝ)*X 1 0+(-89089803/500000000 : ℝ)*X 1 1+(518300449/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674966667/5000000000 : ℝ)*X 2 0+(5183004499/10000000000 : ℝ)*X 2 1+(-890898029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209620219/500000000 : ℝ)*X 0 0+(482689133/1250000000 : ℝ)*X 0 1+(4543884083/10000000000 : ℝ)*X 0 2+(209620219/500000000 : ℝ)*X 1 0+(482689133/1250000000 : ℝ)*X 1 1+(4543884083/10000000000 : ℝ)*X 1 2+(209620219/500000000 : ℝ)*X 2 0+(482689133/1250000000 : ℝ)*X 2 1+(4543884083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-164339859/1000000000 : ℝ)*X 0 0+(64812793/125000000 : ℝ)*X 0 1+(136244527/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639128437/5000000000 : ℝ)*X 1 0+(-378754869/2500000000 : ℝ)*X 1 1+(2724890541/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278256879/10000000000 : ℝ)*X 2 0+(1362445269/2500000000 : ℝ)*X 2 1+(-1515019477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2096286311/5000000000 : ℝ)*X 0 0+(2269379577/5000000000 : ℝ)*X 0 1+(1933345933/5000000000 : ℝ)*X 0 2+(2096286311/5000000000 : ℝ)*X 1 0+(2269379577/5000000000 : ℝ)*X 1 1+(1933345933/5000000000 : ℝ)*X 1 2+(2096286311/5000000000 : ℝ)*X 2 0+(2269379577/5000000000 : ℝ)*X 2 1+(1933345933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (160803634078835642917059669/14305000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180954349/10000000000000 : ℝ)*(base19) + (1688935647/100000000000000 : ℝ)*(base23) + (31146181/50000000000000 : ℝ)*(lower2) + (34476547/12500000000000 : ℝ)*(upper3) + (193487331/100000000000000 : ℝ)*(upper5) + (129638699927677/5000000000000 : ℝ)*(major0) + (129638699927677/5000000000000 : ℝ)*(major1) + (129638699927677/5000000000000 : ℝ)*(major2) + (930007276056229/25000000000000 : ℝ)*(sp0) + (1860024717200161/50000000000000 : ℝ)*(sp1) + (1860024777504083/50000000000000 : ℝ)*(sp2) + (293097374844683/20000000000000 : ℝ)*(sp3) + (1383732431/6250000000000 : ℝ)*(sp4) + (9504237213/100000000000000 : ℝ)*(sp7) + (366374094615157/25000000000000 : ℝ)*(f.failure) + (930012810985953/25000000000000 : ℝ)*(f.sum) + (3423908013763/1430500000000000000000000000 : ℝ)*base66 + (452723232710577259/28610000000000000000000000000000 : ℝ)*base68 + (368415830160227259/28610000000000000000000000000000 : ℝ)*base70 + (166902823477817259/28610000000000000000000000000000 : ℝ)*base72 + (5878447574803/1430500000000000000000000000 : ℝ)*base74 + (36171803594187259/28610000000000000000000000000000 : ℝ)*base76 + (405826935147857259/28610000000000000000000000000000 : ℝ)*base78 + (287913239581117259/28610000000000000000000000000000 : ℝ)*base80 + (723000139219/2861000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6771151/500000000000000000000 : ℝ)*base89 + (6771151/500000000000000000000 : ℝ)*base91 + (6771151/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2981475491134711756018431837/286100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1559470353/100000000000000 : ℝ)*(base19) + (1703203759/100000000000000 : ℝ)*(base23) + (484431983/100000000000000 : ℝ)*(lower1) + (112958287/50000000000000 : ℝ)*(upper3) + (3118987/5000000000000 : ℝ)*(lower4) + (4317577/2000000000000 : ℝ)*(upper5) + (2632479520150263/100000000000000 : ℝ)*(major0) + (2632479520150263/100000000000000 : ℝ)*(major1) + (2632479520150263/100000000000000 : ℝ)*(major2) + (1618095031/100000000000000 : ℝ)*(sp2) + (94425495673749/2500000000000 : ℝ)*(sp4) + (1888509133739803/50000000000000 : ℝ)*(sp5) + (377701650565117/10000000000000 : ℝ)*(sp6) + (371984716495173/25000000000000 : ℝ)*(sp7) + (371984716495173/25000000000000 : ℝ)*(f.failure) + (94425495673749/2500000000000 : ℝ)*(f.sum) + (20015147787379/14305000000000000000000000000 : ℝ)*base66 + (12243894196944797279/572200000000000000000000000000000 : ℝ)*base67 + (3063881212764002721/572200000000000000000000000000000 : ℝ)*base70 + (17988298010075202721/572200000000000000000000000000000 : ℝ)*base72 + (33139513003781/14305000000000000000000000000 : ℝ)*base73 + (16113483673633597279/572200000000000000000000000000000 : ℝ)*base75 + (2727294940183202721/572200000000000000000000000000000 : ℝ)*base78 + (629885396961002721/572200000000000000000000000000000 : ℝ)*base80 + (25028903127821/14305000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5240961/500000000000000000000 : ℝ)*base90 + (5240961/500000000000000000000 : ℝ)*base92 + (5240961/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1635_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5291/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1635_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1635_s5_0 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1643337347/10000000000 : ℝ)*x 0 + (5451797483/10000000000 : ℝ)*x 1 + (2591512451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1643337347/10000000000 : ℝ)^4859 ≤ (126830739951/1250000000000 : ℝ)^3835 := by
    have hnat : (1643337347 : ℕ)^4859*1250000000000^3835 ≤ 126830739951^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643337347 10000000000 126830739951 1250000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451797483/10000000000 : ℝ)^4859 ≤ (46365189614743/100000000000000 : ℝ)^3835 := by
    have hnat : (5451797483 : ℕ)^4859*100000000000000^3835 ≤ 46365189614743^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451797483 10000000000 46365189614743 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591512451/5000000000 : ℝ)^4859 ≤ (10872087791611/25000000000000 : ℝ)^3835 := by
    have hnat : (2591512451 : ℕ)^4859*25000000000000^3835 ≤ 10872087791611^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591512451 5000000000 10872087791611 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1643337347/10000000000 : ℝ), (5451797483/10000000000 : ℝ), (2591512451/5000000000 : ℝ)] ![(126830739951/1250000000000 : ℝ), (46365189614743/100000000000000 : ℝ), (10872087791611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1643337347/10000000000 : ℝ)|^4859 ≤ (126830739951/1250000000000 : ℝ)^3835
        have hw : |(-1643337347/10000000000 : ℝ)|=(1643337347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451797483/10000000000 : ℝ)|^4859 ≤ (46365189614743/100000000000000 : ℝ)^3835
        have hw : |(5451797483/10000000000 : ℝ)|=(5451797483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591512451/5000000000 : ℝ)|^4859 ≤ (10872087791611/25000000000000 : ℝ)^3835
        have hw : |(2591512451/5000000000 : ℝ)|=(2591512451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s5_1 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349926869/10000000000 : ℝ)*x 0 + (-890888803/5000000000 : ℝ)*x 1 + (5183024893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349926869/10000000000 : ℝ)^4859 ≤ (45270242852069/100000000000000 : ℝ)^3835 := by
    have hnat : (5349926869 : ℕ)^4859*100000000000000^3835 ≤ 45270242852069^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349926869 10000000000 45270242852069 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890888803/5000000000 : ℝ)^4859 ≤ (11241406065671/100000000000000 : ℝ)^3835 := by
    have hnat : (890888803 : ℕ)^4859*100000000000000^3835 ≤ 11241406065671^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890888803 5000000000 11241406065671 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183024893/10000000000 : ℝ)^4859 ≤ (21744175535383/50000000000000 : ℝ)^3835 := by
    have hnat : (5183024893 : ℕ)^4859*50000000000000^3835 ≤ 21744175535383^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183024893 10000000000 21744175535383 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349926869/10000000000 : ℝ), (-890888803/5000000000 : ℝ), (5183024893/10000000000 : ℝ)] ![(45270242852069/100000000000000 : ℝ), (11241406065671/100000000000000 : ℝ), (21744175535383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349926869/10000000000 : ℝ)|^4859 ≤ (45270242852069/100000000000000 : ℝ)^3835
        have hw : |(5349926869/10000000000 : ℝ)|=(5349926869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890888803/5000000000 : ℝ)|^4859 ≤ (11241406065671/100000000000000 : ℝ)^3835
        have hw : |(-890888803/5000000000 : ℝ)|=(890888803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183024893/10000000000 : ℝ)|^4859 ≤ (21744175535383/50000000000000 : ℝ)^3835
        have hw : |(5183024893/10000000000 : ℝ)|=(5183024893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s5_2 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349926841/10000000000 : ℝ)*x 0 + (80984763/156250000 : ℝ)*x 1 + (-71271109/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349926841/10000000000 : ℝ)^4859 ≤ (22635121275937/50000000000000 : ℝ)^3835 := by
    have hnat : (5349926841 : ℕ)^4859*50000000000000^3835 ≤ 22635121275937^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349926841 10000000000 22635121275937 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80984763/156250000 : ℝ)^4859 ≤ (43488350422279/100000000000000 : ℝ)^3835 := by
    have hnat : (80984763 : ℕ)^4859*100000000000000^3835 ≤ 43488350422279^3835*156250000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80984763 156250000 43488350422279 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71271109/400000000 : ℝ)^4859 ≤ (11241407016923/100000000000000 : ℝ)^3835 := by
    have hnat : (71271109 : ℕ)^4859*100000000000000^3835 ≤ 11241407016923^3835*400000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71271109 400000000 11241407016923 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349926841/10000000000 : ℝ), (80984763/156250000 : ℝ), (-71271109/400000000 : ℝ)] ![(22635121275937/50000000000000 : ℝ), (43488350422279/100000000000000 : ℝ), (11241407016923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349926841/10000000000 : ℝ)|^4859 ≤ (22635121275937/50000000000000 : ℝ)^3835
        have hw : |(5349926841/10000000000 : ℝ)|=(5349926841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80984763/156250000 : ℝ)|^4859 ≤ (43488350422279/100000000000000 : ℝ)^3835
        have hw : |(80984763/156250000 : ℝ)|=(80984763/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71271109/400000000 : ℝ)|^4859 ≤ (11241407016923/100000000000000 : ℝ)^3835
        have hw : |(-71271109/400000000 : ℝ)|=(71271109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s5_3 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4192407383/10000000000 : ℝ)*x 0 + (1930784399/5000000000 : ℝ)*x 1 + (227191389/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192407383/10000000000 : ℝ)^4859 ≤ (33239601693513/100000000000000 : ℝ)^3835 := by
    have hnat : (4192407383 : ℕ)^4859*100000000000000^3835 ≤ 33239601693513^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192407383 10000000000 33239601693513 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930784399/5000000000 : ℝ)^4859 ≤ (7487964680579/25000000000000 : ℝ)^3835 := by
    have hnat : (1930784399 : ℕ)^4859*25000000000000^3835 ≤ 7487964680579^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930784399 5000000000 7487964680579 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227191389/500000000 : ℝ)^4859 ≤ (36808539569617/100000000000000 : ℝ)^3835 := by
    have hnat : (227191389 : ℕ)^4859*100000000000000^3835 ≤ 36808539569617^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227191389 500000000 36808539569617 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192407383/10000000000 : ℝ), (1930784399/5000000000 : ℝ), (227191389/500000000 : ℝ)] ![(33239601693513/100000000000000 : ℝ), (7487964680579/25000000000000 : ℝ), (36808539569617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192407383/10000000000 : ℝ)|^4859 ≤ (33239601693513/100000000000000 : ℝ)^3835
        have hw : |(4192407383/10000000000 : ℝ)|=(4192407383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1930784399/5000000000 : ℝ)|^4859 ≤ (7487964680579/25000000000000 : ℝ)^3835
        have hw : |(1930784399/5000000000 : ℝ)|=(1930784399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227191389/500000000 : ℝ)|^4859 ≤ (36808539569617/100000000000000 : ℝ)^3835
        have hw : |(227191389/500000000 : ℝ)|=(227191389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s5_4 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1643403457/10000000000 : ℝ)*x 0 + (5185043353/10000000000 : ℝ)*x 1 + (681219737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1643403457/10000000000 : ℝ)^4859 ≤ (1014697637261/10000000000000 : ℝ)^3835 := by
    have hnat : (1643403457 : ℕ)^4859*10000000000000^3835 ≤ 1014697637261^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643403457 10000000000 1014697637261 10000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185043353/10000000000 : ℝ)^4859 ≤ (10877452572317/25000000000000 : ℝ)^3835 := by
    have hnat : (5185043353 : ℕ)^4859*25000000000000^3835 ≤ 10877452572317^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185043353 10000000000 10877452572317 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681219737/1250000000 : ℝ)^4859 ≤ (46343213323739/100000000000000 : ℝ)^3835 := by
    have hnat : (681219737 : ℕ)^4859*100000000000000^3835 ≤ 46343213323739^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681219737 1250000000 46343213323739 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1643403457/10000000000 : ℝ), (5185043353/10000000000 : ℝ), (681219737/1250000000 : ℝ)] ![(1014697637261/10000000000000 : ℝ), (10877452572317/25000000000000 : ℝ), (46343213323739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1643403457/10000000000 : ℝ)|^4859 ≤ (1014697637261/10000000000000 : ℝ)^3835
        have hw : |(-1643403457/10000000000 : ℝ)|=(1643403457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185043353/10000000000 : ℝ)|^4859 ≤ (10877452572317/25000000000000 : ℝ)^3835
        have hw : |(5185043353/10000000000 : ℝ)|=(5185043353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681219737/1250000000 : ℝ)|^4859 ≤ (46343213323739/100000000000000 : ℝ)^3835
        have hw : |(681219737/1250000000 : ℝ)|=(681219737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s5_5 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055652437/2000000000 : ℝ)*x 0 + (-303008911/2000000000 : ℝ)*x 1 + (2724878999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055652437/2000000000 : ℝ)^4859 ≤ (22251642272589/50000000000000 : ℝ)^3835 := by
    have hnat : (1055652437 : ℕ)^4859*50000000000000^3835 ≤ 22251642272589^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055652437 2000000000 22251642272589 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303008911/2000000000 : ℝ)^4859 ≤ (9153501015007/100000000000000 : ℝ)^3835 := by
    have hnat : (303008911 : ℕ)^4859*100000000000000^3835 ≤ 9153501015007^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303008911 2000000000 9153501015007 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724878999/5000000000 : ℝ)^4859 ≤ (23171607211361/50000000000000 : ℝ)^3835 := by
    have hnat : (2724878999 : ℕ)^4859*50000000000000^3835 ≤ 23171607211361^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724878999 5000000000 23171607211361 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055652437/2000000000 : ℝ), (-303008911/2000000000 : ℝ), (2724878999/5000000000 : ℝ)] ![(22251642272589/50000000000000 : ℝ), (9153501015007/100000000000000 : ℝ), (23171607211361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055652437/2000000000 : ℝ)|^4859 ≤ (22251642272589/50000000000000 : ℝ)^3835
        have hw : |(1055652437/2000000000 : ℝ)|=(1055652437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-303008911/2000000000 : ℝ)|^4859 ≤ (9153501015007/100000000000000 : ℝ)^3835
        have hw : |(-303008911/2000000000 : ℝ)|=(303008911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724878999/5000000000 : ℝ)|^4859 ≤ (23171607211361/50000000000000 : ℝ)^3835
        have hw : |(2724878999/5000000000 : ℝ)|=(2724878999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s5_6 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263913113/500000000 : ℝ)*x 0 + (1362439489/2500000000 : ℝ)*x 1 + (-151504451/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263913113/500000000 : ℝ)^4859 ≤ (2781455334149/6250000000000 : ℝ)^3835 := by
    have hnat : (263913113 : ℕ)^4859*6250000000000^3835 ≤ 2781455334149^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263913113 500000000 2781455334149 6250000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362439489/2500000000 : ℝ)^4859 ≤ (46343213970199/100000000000000 : ℝ)^3835 := by
    have hnat : (1362439489 : ℕ)^4859*100000000000000^3835 ≤ 46343213970199^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362439489 2500000000 46343213970199 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151504451/1000000000 : ℝ)^4859 ≤ (9153500670533/100000000000000 : ℝ)^3835 := by
    have hnat : (151504451 : ℕ)^4859*100000000000000^3835 ≤ 9153500670533^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151504451 1000000000 9153500670533 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263913113/500000000 : ℝ), (1362439489/2500000000 : ℝ), (-151504451/1000000000 : ℝ)] ![(2781455334149/6250000000000 : ℝ), (46343213970199/100000000000000 : ℝ), (9153500670533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263913113/500000000 : ℝ)|^4859 ≤ (2781455334149/6250000000000 : ℝ)^3835
        have hw : |(263913113/500000000 : ℝ)|=(263913113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362439489/2500000000 : ℝ)|^4859 ≤ (46343213970199/100000000000000 : ℝ)^3835
        have hw : |(1362439489/2500000000 : ℝ)|=(1362439489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151504451/1000000000 : ℝ)|^4859 ≤ (9153500670533/100000000000000 : ℝ)^3835
        have hw : |(-151504451/1000000000 : ℝ)|=(151504451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s5_7 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524071959/1250000000 : ℝ)*x 0 + (907740901/2000000000 : ℝ)*x 1 + (3866745787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524071959/1250000000 : ℝ)^4859 ≤ (16620646129351/50000000000000 : ℝ)^3835 := by
    have hnat : (524071959 : ℕ)^4859*50000000000000^3835 ≤ 16620646129351^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524071959 1250000000 16620646129351 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907740901/2000000000 : ℝ)^4859 ≤ (1470238528341/4000000000000 : ℝ)^3835 := by
    have hnat : (907740901 : ℕ)^4859*4000000000000^3835 ≤ 1470238528341^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907740901 2000000000 1470238528341 4000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3866745787/10000000000 : ℝ)^4859 ≤ (30002744506883/100000000000000 : ℝ)^3835 := by
    have hnat : (3866745787 : ℕ)^4859*100000000000000^3835 ≤ 30002744506883^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866745787 10000000000 30002744506883 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524071959/1250000000 : ℝ), (907740901/2000000000 : ℝ), (3866745787/10000000000 : ℝ)] ![(16620646129351/50000000000000 : ℝ), (1470238528341/4000000000000 : ℝ), (30002744506883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524071959/1250000000 : ℝ)|^4859 ≤ (16620646129351/50000000000000 : ℝ)^3835
        have hw : |(524071959/1250000000 : ℝ)|=(524071959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(907740901/2000000000 : ℝ)|^4859 ≤ (1470238528341/4000000000000 : ℝ)^3835
        have hw : |(907740901/2000000000 : ℝ)|=(907740901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3866745787/10000000000 : ℝ)|^4859 ≤ (30002744506883/100000000000000 : ℝ)^3835
        have hw : |(3866745787/10000000000 : ℝ)|=(3866745787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1635_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10589/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2037/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16297/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2647/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16297/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2647/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16297/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2647/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16297/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2647/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16297/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2647/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16297/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2647/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2647/25000 : ℝ) ^ (4855/1024 : ℝ) ≤ (594808491587809/25000000000000000000 : ℝ) := by
    have hpowers : (2647/25000 : ℝ)^4855 ≤ (594808491587809/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2647 : ℕ)^4855*25000000000000000000^1024 ≤ 594808491587809^1024*25000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2647 25000 594808491587809 25000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2647/25000 : ℝ)) (X := (594808491587809/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16297/100000 : ℝ) ^ (4855/1024 : ℝ) ≤ (9191920312289969/50000000000000000000 : ℝ) := by
    have hpowers : (16297/100000 : ℝ)^4855 ≤ (9191920312289969/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16297 : ℕ)^4855*50000000000000000000^1024 ≤ 9191920312289969^1024*100000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16297 100000 9191920312289969 50000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16297/100000 : ℝ)) (X := (9191920312289969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500594808491587809/12500000000000000000 : ℝ) ≤ (10000100362094449/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (12500594808491587809/12500000000000000000 : ℝ)^1024 ≤ (10000100362094449/10000000000000000 : ℝ)^4855 := by
      have hnat : (12500594808491587809 : ℕ)^1024*10000000000000000^4855 ≤ 10000100362094449^4855*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500594808491587809 12500000000000000000 10000100362094449 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000100362094449/10000000000000000 : ℝ)) (X := (12500594808491587809/12500000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010381537295465587/50000000000000000000 : ℝ) ≤ (312513684118747/312500000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (50010381537295465587/50000000000000000000 : ℝ)^1024 ≤ (312513684118747/312500000000000 : ℝ)^4855 := by
      have hnat : (50010381537295465587 : ℕ)^1024*312500000000000^4855 ≤ 312513684118747^4855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010381537295465587 50000000000000000000 312513684118747 312500000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312513684118747/312500000000000 : ℝ)) (X := (50010381537295465587/50000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009191920312289969/25000000000000000000 : ℝ) ≤ (10000775421505359/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (25009191920312289969/25000000000000000000 : ℝ)^1024 ≤ (10000775421505359/10000000000000000 : ℝ)^4855 := by
      have hnat : (25009191920312289969 : ℕ)^1024*10000000000000000^4855 ≤ 10000775421505359^4855*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009191920312289969 25000000000000000000 10000775421505359 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000775421505359/10000000000000000 : ℝ)) (X := (25009191920312289969/25000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(594808491587809/25000000000000000000 : ℝ) ≤ ((57083425438154494261/57090000000000000000 : ℝ)+2*(67505941091/114180000000000 : ℝ)*(2647/25000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (57083425438154494261/57090000000000000000 : ℝ)+2*(67505941091/114180000000000 : ℝ)*(2647/25000 : ℝ)=(10000100362094449/10000000000000000 : ℝ) by norm_num, show 1+2*(594808491587809/25000000000000000000 : ℝ)=(12500594808491587809/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9191920312289969/50000000000000000000 : ℝ)+(594808491587809/25000000000000000000 : ℝ) ≤ ((57083425438154494261/57090000000000000000 : ℝ)+(67505941091/114180000000000 : ℝ)*((16297/100000 : ℝ)+(2647/25000 : ℝ)))^(4855/1024 : ℝ) := by
    rw [show (57083425438154494261/57090000000000000000 : ℝ)+(67505941091/114180000000000 : ℝ)*((16297/100000 : ℝ)+(2647/25000 : ℝ))=(312513684118747/312500000000000 : ℝ) by norm_num, show 1+(9191920312289969/50000000000000000000 : ℝ)+(594808491587809/25000000000000000000 : ℝ)=(50010381537295465587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9191920312289969/50000000000000000000 : ℝ) ≤ ((57083425438154494261/57090000000000000000 : ℝ)+2*(67505941091/114180000000000 : ℝ)*(16297/100000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (57083425438154494261/57090000000000000000 : ℝ)+2*(67505941091/114180000000000 : ℝ)*(16297/100000 : ℝ)=(10000775421505359/10000000000000000 : ℝ) by norm_num, show 1+2*(9191920312289969/50000000000000000000 : ℝ)=(25009191920312289969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57083425438154494261/57090000000000000000 : ℝ)*(X 1 0+X 2 0)+(67505941091/114180000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (16297/100000 : ℝ)) (c := (57083425438154494261/57090000000000000000 : ℝ)) (alpha := (67505941091/114180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57083425438154494261/57090000000000000000 : ℝ)*(X 0 1+X 2 1)+(67505941091/114180000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (16297/100000 : ℝ)) (c := (57083425438154494261/57090000000000000000 : ℝ)) (alpha := (67505941091/114180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57083425438154494261/57090000000000000000 : ℝ)*(X 0 2+X 1 2)+(67505941091/114180000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (16297/100000 : ℝ)) (c := (57083425438154494261/57090000000000000000 : ℝ)) (alpha := (67505941091/114180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1643337347/10000000000 : ℝ)*X 0 0+(5451797483/10000000000 : ℝ)*X 0 1+(2591512451/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349926869/10000000000 : ℝ)*X 1 0+(-890888803/5000000000 : ℝ)*X 1 1+(5183024893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349926841/10000000000 : ℝ)*X 2 0+(80984763/156250000 : ℝ)*X 2 1+(-71271109/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192407383/10000000000 : ℝ)*X 0 0+(1930784399/5000000000 : ℝ)*X 0 1+(227191389/500000000 : ℝ)*X 0 2+(4192407383/10000000000 : ℝ)*X 1 0+(1930784399/5000000000 : ℝ)*X 1 1+(227191389/500000000 : ℝ)*X 1 2+(4192407383/10000000000 : ℝ)*X 2 0+(1930784399/5000000000 : ℝ)*X 2 1+(227191389/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1643403457/10000000000 : ℝ)*X 0 0+(5185043353/10000000000 : ℝ)*X 0 1+(681219737/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055652437/2000000000 : ℝ)*X 1 0+(-303008911/2000000000 : ℝ)*X 1 1+(2724878999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263913113/500000000 : ℝ)*X 2 0+(1362439489/2500000000 : ℝ)*X 2 1+(-151504451/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((524071959/1250000000 : ℝ)*X 0 0+(907740901/2000000000 : ℝ)*X 0 1+(3866745787/10000000000 : ℝ)*X 0 2+(524071959/1250000000 : ℝ)*X 1 0+(907740901/2000000000 : ℝ)*X 1 1+(3866745787/10000000000 : ℝ)*X 1 2+(524071959/1250000000 : ℝ)*X 2 0+(907740901/2000000000 : ℝ)*X 2 1+(3866745787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4872677499805432776585294489/951500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422549713/50000000000000 : ℝ)*(base19) + (795260869/100000000000000 : ℝ)*(base23) + (16245479/100000000000000 : ℝ)*(lower2) + (5093533/3125000000000 : ℝ)*(upper3) + (22873401/50000000000000 : ℝ)*(upper5) + (2593182918713749/100000000000000 : ℝ)*(major0) + (2593182918713749/100000000000000 : ℝ)*(major1) + (2593182918713749/100000000000000 : ℝ)*(major2) + (1860314565758423/50000000000000 : ℝ)*(sp0) + (1860318655973609/50000000000000 : ℝ)*(sp1) + (1860318680892887/50000000000000 : ℝ)*(sp2) + (183215348004601/12500000000000 : ℝ)*(sp3) + (4512764899/50000000000000 : ℝ)*(sp4) + (472564243/10000000000000 : ℝ)*(sp7) + (1465727509679237/100000000000000 : ℝ)*(f.failure) + (930159539261661/25000000000000 : ℝ)*(f.sum) + (39015784339/45672000000000000000000000 : ℝ)*base65 + (691361286387794489/5709000000000000000000000000000000 : ℝ)*base67 + (5771555003948205511/5709000000000000000000000000000000 : ℝ)*base70 + (9260690942192205511/5709000000000000000000000000000000 : ℝ)*base72 + (60525944899/228360000000000000000000000 : ℝ)*base74 + (57790898697914205511/5709000000000000000000000000000000 : ℝ)*base76 + (26554380917979794489/5709000000000000000000000000000000 : ℝ)*base77 + (5520651030716205511/5709000000000000000000000000000000 : ℝ)*base80 + (4017804950341/5709000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5937409/2000000000000000000000 : ℝ)*base90 + (5937409/2000000000000000000000 : ℝ)*base92 + (5937409/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9083193292173037259573/1903000000000000000000000000 : ℝ) := by norm_num
    linear_combination (299946983/50000000000000 : ℝ)*(base19) + (175659767/20000000000000 : ℝ)*(base23) + (169496451/100000000000000 : ℝ)*(lower1) + (142001789/100000000000000 : ℝ)*(upper3) + (84645099/100000000000000 : ℝ)*(lower4) + (6452873/20000000000000 : ℝ)*(upper5) + (2632914575416061/100000000000000 : ℝ)*(major0) + (2632914575416061/100000000000000 : ℝ)*(major1) + (2632914575416061/100000000000000 : ℝ)*(major2) + (948082763/20000000000000 : ℝ)*(sp2) + (944411055589521/25000000000000 : ℝ)*(sp4) + (1888821811232059/50000000000000 : ℝ)*(sp5) + (1888819301822717/50000000000000 : ℝ)*(sp6) + (744092384685483/50000000000000 : ℝ)*(sp7) + (744092384685483/50000000000000 : ℝ)*(f.failure) + (944411055589521/25000000000000 : ℝ)*(f.sum) + (154373458583/45672000000000000000000000 : ℝ)*base65 + (105412861677649225921/5709000000000000000000000000000000 : ℝ)*base67 + (16318055965366774079/5709000000000000000000000000000000 : ℝ)*base70 + (651334847732149225921/5709000000000000000000000000000000 : ℝ)*base71 + (14247747905491/5709000000000000000000000000 : ℝ)*base73 + (196266218375866774079/5709000000000000000000000000000000 : ℝ)*base76 + (24955869453175774079/5709000000000000000000000000000000 : ℝ)*base78 + (24257078383261225921/5709000000000000000000000000000000 : ℝ)*base79 + (1117389253699/713625000000000000000000000 : ℝ)*base82 + (955631/1000000000000000000000 : ℝ)*base90 + (955631/1000000000000000000000 : ℝ)*base92 + (955631/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1635_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10589/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2037/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1635_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1635_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10589/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2037/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1635_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1635_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1635_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10589/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2037/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1635_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
