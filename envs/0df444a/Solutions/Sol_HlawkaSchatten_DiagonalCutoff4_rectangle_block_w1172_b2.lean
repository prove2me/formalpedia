-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:34.945919+00:00
-- url     : https://prove2.me/submissions/968e6593-c24d-4977-89ac-a4f943a59cd3

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
theorem support_rectangle_w1172_s6_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152597881/10000000000 : ℝ)*x 0 + (1078556393/2000000000 : ℝ)*x 1 + (2632967041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152597881/10000000000 : ℝ)^8365 ≤ (1635371693643/12500000000000 : ℝ)^6317 := by
    have hnat : (2152597881 : ℕ)^8365*12500000000000^6317 ≤ 1635371693643^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152597881 10000000000 1635371693643 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078556393/2000000000 : ℝ)^8365 ≤ (44143359045339/100000000000000 : ℝ)^6317 := by
    have hnat : (1078556393 : ℕ)^8365*100000000000000^6317 ≤ 44143359045339^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078556393 2000000000 44143359045339 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632967041/5000000000 : ℝ)^8365 ≤ (10693416847481/25000000000000 : ℝ)^6317 := by
    have hnat : (2632967041 : ℕ)^8365*25000000000000^6317 ≤ 10693416847481^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632967041 5000000000 10693416847481 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152597881/10000000000 : ℝ), (1078556393/2000000000 : ℝ), (2632967041/5000000000 : ℝ)] ![(1635371693643/12500000000000 : ℝ), (44143359045339/100000000000000 : ℝ), (10693416847481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152597881/10000000000 : ℝ)|^8365 ≤ (1635371693643/12500000000000 : ℝ)^6317
        have hw : |(-2152597881/10000000000 : ℝ)|=(2152597881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078556393/2000000000 : ℝ)|^8365 ≤ (44143359045339/100000000000000 : ℝ)^6317
        have hw : |(1078556393/2000000000 : ℝ)|=(1078556393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632967041/5000000000 : ℝ)|^8365 ≤ (10693416847481/25000000000000 : ℝ)^6317
        have hw : |(2632967041/5000000000 : ℝ)|=(2632967041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s6_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534471327/1000000000 : ℝ)*x 0 + (-2216933609/10000000000 : ℝ)*x 1 + (1316483653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534471327/1000000000 : ℝ)^8365 ≤ (34080527181/78125000000 : ℝ)^6317 := by
    have hnat : (534471327 : ℕ)^8365*78125000000^6317 ≤ 34080527181^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534471327 1000000000 34080527181 78125000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216933609/10000000000 : ℝ)^8365 ≤ (13603252098271/100000000000000 : ℝ)^6317 := by
    have hnat : (2216933609 : ℕ)^8365*100000000000000^6317 ≤ 13603252098271^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216933609 10000000000 13603252098271 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316483653/2500000000 : ℝ)^8365 ≤ (21386836545337/50000000000000 : ℝ)^6317 := by
    have hnat : (1316483653 : ℕ)^8365*50000000000000^6317 ≤ 21386836545337^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316483653 2500000000 21386836545337 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534471327/1000000000 : ℝ), (-2216933609/10000000000 : ℝ), (1316483653/2500000000 : ℝ)] ![(34080527181/78125000000 : ℝ), (13603252098271/100000000000000 : ℝ), (21386836545337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534471327/1000000000 : ℝ)|^8365 ≤ (34080527181/78125000000 : ℝ)^6317
        have hw : |(534471327/1000000000 : ℝ)|=(534471327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216933609/10000000000 : ℝ)|^8365 ≤ (13603252098271/100000000000000 : ℝ)^6317
        have hw : |(-2216933609/10000000000 : ℝ)|=(2216933609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316483653/2500000000 : ℝ)|^8365 ≤ (21386836545337/50000000000000 : ℝ)^6317
        have hw : |(1316483653/2500000000 : ℝ)|=(1316483653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s6_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344713319/10000000000 : ℝ)*x 0 + (1053186711/2000000000 : ℝ)*x 1 + (-2216934943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344713319/10000000000 : ℝ)^8365 ≤ (21811537660637/50000000000000 : ℝ)^6317 := by
    have hnat : (5344713319 : ℕ)^8365*50000000000000^6317 ≤ 21811537660637^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344713319 10000000000 21811537660637 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053186711/2000000000 : ℝ)^8365 ≤ (42773661721443/100000000000000 : ℝ)^6317 := by
    have hnat : (1053186711 : ℕ)^8365*100000000000000^6317 ≤ 42773661721443^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053186711 2000000000 42773661721443 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216934943/10000000000 : ℝ)^8365 ≤ (2720652587513/20000000000000 : ℝ)^6317 := by
    have hnat : (2216934943 : ℕ)^8365*20000000000000^6317 ≤ 2720652587513^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216934943 10000000000 2720652587513 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344713319/10000000000 : ℝ), (1053186711/2000000000 : ℝ), (-2216934943/10000000000 : ℝ)] ![(21811537660637/50000000000000 : ℝ), (42773661721443/100000000000000 : ℝ), (2720652587513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344713319/10000000000 : ℝ)|^8365 ≤ (21811537660637/50000000000000 : ℝ)^6317
        have hw : |(5344713319/10000000000 : ℝ)|=(5344713319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053186711/2000000000 : ℝ)|^8365 ≤ (42773661721443/100000000000000 : ℝ)^6317
        have hw : |(1053186711/2000000000 : ℝ)|=(1053186711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2216934943/10000000000 : ℝ)|^8365 ≤ (2720652587513/20000000000000 : ℝ)^6317
        have hw : |(-2216934943/10000000000 : ℝ)|=(2216934943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s6_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360449179/10000000000 : ℝ)*x 0 + (4235350671/10000000000 : ℝ)*x 1 + (2244599447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360449179/10000000000 : ℝ)^8365 ≤ (33316979502429/100000000000000 : ℝ)^6317 := by
    have hnat : (4360449179 : ℕ)^8365*100000000000000^6317 ≤ 33316979502429^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360449179 10000000000 33316979502429 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235350671/10000000000 : ℝ)^8365 ≤ (32057172926163/100000000000000 : ℝ)^6317 := by
    have hnat : (4235350671 : ℕ)^8365*100000000000000^6317 ≤ 32057172926163^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235350671 10000000000 32057172926163 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244599447/5000000000 : ℝ)^8365 ≤ (34625847561191/100000000000000 : ℝ)^6317 := by
    have hnat : (2244599447 : ℕ)^8365*100000000000000^6317 ≤ 34625847561191^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244599447 5000000000 34625847561191 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360449179/10000000000 : ℝ), (4235350671/10000000000 : ℝ), (2244599447/5000000000 : ℝ)] ![(33316979502429/100000000000000 : ℝ), (32057172926163/100000000000000 : ℝ), (34625847561191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360449179/10000000000 : ℝ)|^8365 ≤ (33316979502429/100000000000000 : ℝ)^6317
        have hw : |(4360449179/10000000000 : ℝ)|=(4360449179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235350671/10000000000 : ℝ)|^8365 ≤ (32057172926163/100000000000000 : ℝ)^6317
        have hw : |(4235350671/10000000000 : ℝ)|=(4235350671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244599447/5000000000 : ℝ)|^8365 ≤ (34625847561191/100000000000000 : ℝ)^6317
        have hw : |(2244599447/5000000000 : ℝ)|=(2244599447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s6_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269075327/1250000000 : ℝ)*x 0 + (5266254299/10000000000 : ℝ)*x 1 + (337028793/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269075327/1250000000 : ℝ)^8365 ≤ (13083011657373/100000000000000 : ℝ)^6317 := by
    have hnat : (269075327 : ℕ)^8365*100000000000000^6317 ≤ 13083011657373^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269075327 1250000000 13083011657373 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266254299/10000000000 : ℝ)^8365 ≤ (42777111720313/100000000000000 : ℝ)^6317 := by
    have hnat : (5266254299 : ℕ)^8365*100000000000000^6317 ≤ 42777111720313^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266254299 10000000000 42777111720313 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337028793/625000000 : ℝ)^8365 ≤ (22069938305143/50000000000000 : ℝ)^6317 := by
    have hnat : (337028793 : ℕ)^8365*50000000000000^6317 ≤ 22069938305143^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337028793 625000000 22069938305143 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269075327/1250000000 : ℝ), (5266254299/10000000000 : ℝ), (337028793/625000000 : ℝ)] ![(13083011657373/100000000000000 : ℝ), (42777111720313/100000000000000 : ℝ), (22069938305143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269075327/1250000000 : ℝ)|^8365 ≤ (13083011657373/100000000000000 : ℝ)^6317
        have hw : |(-269075327/1250000000 : ℝ)|=(269075327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266254299/10000000000 : ℝ)|^8365 ≤ (42777111720313/100000000000000 : ℝ)^6317
        have hw : |(5266254299/10000000000 : ℝ)|=(5266254299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337028793/625000000 : ℝ)|^8365 ≤ (22069938305143/50000000000000 : ℝ)^6317
        have hw : |(337028793/625000000 : ℝ)|=(337028793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s6_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312505529/10000000000 : ℝ)*x 0 + (-8361629/40000000 : ℝ)*x 1 + (5392460689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312505529/10000000000 : ℝ)^8365 ≤ (4327531275313/10000000000000 : ℝ)^6317 := by
    have hnat : (5312505529 : ℕ)^8365*10000000000000^6317 ≤ 4327531275313^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312505529 10000000000 4327531275313 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8361629/40000000 : ℝ)^8365 ≤ (6292405303019/50000000000000 : ℝ)^6317 := by
    have hnat : (8361629 : ℕ)^8365*50000000000000^6317 ≤ 6292405303019^6317*40000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8361629 40000000 6292405303019 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392460689/10000000000 : ℝ)^8365 ≤ (22069938310563/50000000000000 : ℝ)^6317 := by
    have hnat : (5392460689 : ℕ)^8365*50000000000000^6317 ≤ 22069938310563^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392460689 10000000000 22069938310563 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312505529/10000000000 : ℝ), (-8361629/40000000 : ℝ), (5392460689/10000000000 : ℝ)] ![(4327531275313/10000000000000 : ℝ), (6292405303019/50000000000000 : ℝ), (22069938310563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312505529/10000000000 : ℝ)|^8365 ≤ (4327531275313/10000000000000 : ℝ)^6317
        have hw : |(5312505529/10000000000 : ℝ)|=(5312505529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8361629/40000000 : ℝ)|^8365 ≤ (6292405303019/50000000000000 : ℝ)^6317
        have hw : |(-8361629/40000000 : ℝ)|=(8361629/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392460689/10000000000 : ℝ)|^8365 ≤ (22069938310563/50000000000000 : ℝ)^6317
        have hw : |(5392460689/10000000000 : ℝ)|=(5392460689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s6_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312505531/10000000000 : ℝ)*x 0 + (5392460689/10000000000 : ℝ)*x 1 + (-130650453/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312505531/10000000000 : ℝ)^8365 ≤ (2704707048419/6250000000000 : ℝ)^6317 := by
    have hnat : (5312505531 : ℕ)^8365*6250000000000^6317 ≤ 2704707048419^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312505531 10000000000 2704707048419 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392460689/10000000000 : ℝ)^8365 ≤ (22069938310563/50000000000000 : ℝ)^6317 := by
    have hnat : (5392460689 : ℕ)^8365*50000000000000^6317 ≤ 22069938310563^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392460689 10000000000 22069938310563 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130650453/625000000 : ℝ)^8365 ≤ (6292405295047/50000000000000 : ℝ)^6317 := by
    have hnat : (130650453 : ℕ)^8365*50000000000000^6317 ≤ 6292405295047^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130650453 625000000 6292405295047 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312505531/10000000000 : ℝ), (5392460689/10000000000 : ℝ), (-130650453/625000000 : ℝ)] ![(2704707048419/6250000000000 : ℝ), (22069938310563/50000000000000 : ℝ), (6292405295047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312505531/10000000000 : ℝ)|^8365 ≤ (2704707048419/6250000000000 : ℝ)^6317
        have hw : |(5312505531/10000000000 : ℝ)|=(5312505531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392460689/10000000000 : ℝ)|^8365 ≤ (22069938310563/50000000000000 : ℝ)^6317
        have hw : |(5392460689/10000000000 : ℝ)|=(5392460689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130650453/625000000 : ℝ)|^8365 ≤ (6292405295047/50000000000000 : ℝ)^6317
        have hw : |(-130650453/625000000 : ℝ)|=(130650453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s6_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360459123/10000000000 : ℝ)*x 0 + (2244278597/5000000000 : ℝ)*x 1 + (2117997263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360459123/10000000000 : ℝ)^8365 ≤ (33317080114651/100000000000000 : ℝ)^6317 := by
    have hnat : (4360459123 : ℕ)^8365*100000000000000^6317 ≤ 33317080114651^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360459123 10000000000 33317080114651 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244278597/5000000000 : ℝ)^8365 ≤ (17309646764203/50000000000000 : ℝ)^6317 := by
    have hnat : (2244278597 : ℕ)^8365*50000000000000^6317 ≤ 17309646764203^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244278597 5000000000 17309646764203 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117997263/5000000000 : ℝ)^8365 ≤ (6412725268513/20000000000000 : ℝ)^6317 := by
    have hnat : (2117997263 : ℕ)^8365*20000000000000^6317 ≤ 6412725268513^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117997263 5000000000 6412725268513 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360459123/10000000000 : ℝ), (2244278597/5000000000 : ℝ), (2117997263/5000000000 : ℝ)] ![(33317080114651/100000000000000 : ℝ), (17309646764203/50000000000000 : ℝ), (6412725268513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360459123/10000000000 : ℝ)|^8365 ≤ (33317080114651/100000000000000 : ℝ)^6317
        have hw : |(4360459123/10000000000 : ℝ)|=(4360459123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244278597/5000000000 : ℝ)|^8365 ≤ (17309646764203/50000000000000 : ℝ)^6317
        have hw : |(2244278597/5000000000 : ℝ)|=(2244278597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117997263/5000000000 : ℝ)|^8365 ≤ (6412725268513/20000000000000 : ℝ)^6317
        have hw : |(2117997263/5000000000 : ℝ)|=(2117997263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5693/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (5679/50000 : ℝ) ^ (2091/512 : ℝ) ≤ (13863330436713893/100000000000000000000 : ℝ) := by
    have hpowers : (5679/50000 : ℝ)^2091 ≤ (13863330436713893/100000000000000000000 : ℝ)^512 := by
      have hnat : (5679 : ℕ)^2091*100000000000000000000^512 ≤ 13863330436713893^512*50000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5679 50000 13863330436713893 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5679/50000 : ℝ)) (X := (13863330436713893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14101/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (3353898659853619/10000000000000000000 : ℝ) := by
    have hpowers : (14101/100000 : ℝ)^2091 ≤ (3353898659853619/10000000000000000000 : ℝ)^512 := by
      have hnat : (14101 : ℕ)^2091*10000000000000000000^512 ≤ 3353898659853619^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14101 100000 3353898659853619 10000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14101/100000 : ℝ)) (X := (3353898659853619/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013863330436713893/50000000000000000000 : ℝ) ≤ (5000339420479587/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50013863330436713893/50000000000000000000 : ℝ)^512 ≤ (5000339420479587/5000000000000000 : ℝ)^2091 := by
      have hnat : (50013863330436713893 : ℕ)^512*5000000000000000^2091 ≤ 5000339420479587^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013863330436713893 50000000000000000000 5000339420479587 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000339420479587/5000000000000000 : ℝ)) (X := (50013863330436713893/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047402317035250083/100000000000000000000 : ℝ) ≤ (625072530020781/625000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (100047402317035250083/100000000000000000000 : ℝ)^512 ≤ (625072530020781/625000000000000 : ℝ)^2091 := by
      have hnat : (100047402317035250083 : ℕ)^512*625000000000000^2091 ≤ 625072530020781^2091*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047402317035250083 100000000000000000000 625072530020781 625000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625072530020781/625000000000000 : ℝ)) (X := (100047402317035250083/100000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003353898659853619/5000000000000000000 : ℝ) ≤ (5000821059852909/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (5003353898659853619/5000000000000000000 : ℝ)^512 ≤ (5000821059852909/5000000000000000 : ℝ)^2091 := by
      have hnat : (5003353898659853619 : ℕ)^512*5000000000000000^2091 ≤ 5000821059852909^2091*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003353898659853619 5000000000000000000 5000821059852909 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000821059852909/5000000000000000 : ℝ)) (X := (5003353898659853619/5000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13863330436713893/100000000000000000000 : ℝ) ≤ ((2742092114074663173/2743000000000000000 : ℝ)+2*(240819686661/137150000000000 : ℝ)*(5679/50000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (2742092114074663173/2743000000000000000 : ℝ)+2*(240819686661/137150000000000 : ℝ)*(5679/50000 : ℝ)=(5000339420479587/5000000000000000 : ℝ) by norm_num, show 1+2*(13863330436713893/100000000000000000000 : ℝ)=(50013863330436713893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3353898659853619/10000000000000000000 : ℝ)+(13863330436713893/100000000000000000000 : ℝ) ≤ ((2742092114074663173/2743000000000000000 : ℝ)+(240819686661/137150000000000 : ℝ)*((14101/100000 : ℝ)+(5679/50000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (2742092114074663173/2743000000000000000 : ℝ)+(240819686661/137150000000000 : ℝ)*((14101/100000 : ℝ)+(5679/50000 : ℝ))=(625072530020781/625000000000000 : ℝ) by norm_num, show 1+(3353898659853619/10000000000000000000 : ℝ)+(13863330436713893/100000000000000000000 : ℝ)=(100047402317035250083/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3353898659853619/10000000000000000000 : ℝ) ≤ ((2742092114074663173/2743000000000000000 : ℝ)+2*(240819686661/137150000000000 : ℝ)*(14101/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (2742092114074663173/2743000000000000000 : ℝ)+2*(240819686661/137150000000000 : ℝ)*(14101/100000 : ℝ)=(5000821059852909/5000000000000000 : ℝ) by norm_num, show 1+2*(3353898659853619/10000000000000000000 : ℝ)=(5003353898659853619/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2742092114074663173/2743000000000000000 : ℝ)*(X 1 0+X 2 0)+(240819686661/137150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (2742092114074663173/2743000000000000000 : ℝ)) (alpha := (240819686661/137150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2742092114074663173/2743000000000000000 : ℝ)*(X 0 1+X 2 1)+(240819686661/137150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (2742092114074663173/2743000000000000000 : ℝ)) (alpha := (240819686661/137150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2742092114074663173/2743000000000000000 : ℝ)*(X 0 2+X 1 2)+(240819686661/137150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (2742092114074663173/2743000000000000000 : ℝ)) (alpha := (240819686661/137150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152597881/10000000000 : ℝ)*X 0 0+(1078556393/2000000000 : ℝ)*X 0 1+(2632967041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534471327/1000000000 : ℝ)*X 1 0+(-2216933609/10000000000 : ℝ)*X 1 1+(1316483653/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344713319/10000000000 : ℝ)*X 2 0+(1053186711/2000000000 : ℝ)*X 2 1+(-2216934943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360449179/10000000000 : ℝ)*X 0 0+(4235350671/10000000000 : ℝ)*X 0 1+(2244599447/5000000000 : ℝ)*X 0 2+(4360449179/10000000000 : ℝ)*X 1 0+(4235350671/10000000000 : ℝ)*X 1 1+(2244599447/5000000000 : ℝ)*X 1 2+(4360449179/10000000000 : ℝ)*X 2 0+(4235350671/10000000000 : ℝ)*X 2 1+(2244599447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269075327/1250000000 : ℝ)*X 0 0+(5266254299/10000000000 : ℝ)*X 0 1+(337028793/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312505529/10000000000 : ℝ)*X 1 0+(-8361629/40000000 : ℝ)*X 1 1+(5392460689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312505531/10000000000 : ℝ)*X 2 0+(5392460689/10000000000 : ℝ)*X 2 1+(-130650453/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360459123/10000000000 : ℝ)*X 0 0+(2244278597/5000000000 : ℝ)*X 0 1+(2117997263/5000000000 : ℝ)*X 0 2+(4360459123/10000000000 : ℝ)*X 1 0+(2244278597/5000000000 : ℝ)*X 1 1+(2117997263/5000000000 : ℝ)*X 1 2+(4360459123/10000000000 : ℝ)*X 2 0+(2244278597/5000000000 : ℝ)*X 2 1+(2117997263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26010729593861608810013403/4285937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7588703/100000000000000 : ℝ)*(base21) + (9679291/6250000000000 : ℝ)*(upper2) + (29142733/10000000000000 : ℝ)*(upper3) + (7148401/50000000000000 : ℝ)*(lower4) + (369466001727663/6250000000000 : ℝ)*(major0) + (369466001727663/6250000000000 : ℝ)*(major1) + (369466001727663/6250000000000 : ℝ)*(major2) + (3941745342938617/50000000000000 : ℝ)*(sp0) + (7883500675729101/100000000000000 : ℝ)*(sp1) + (1576687010879081/20000000000000 : ℝ)*(sp2) + (1969692512808811/50000000000000 : ℝ)*(sp3) + (9989851867/100000000000000 : ℝ)*(sp4) + (32806872497/50000000000000 : ℝ)*(sp6) + (26151643337/100000000000000 : ℝ)*(sp7) + (3939411177260959/100000000000000 : ℝ)*(f.failure) + (7883500675729101/100000000000000 : ℝ)*(f.sum) + (58050512317769/13715000000000000000000000000 : ℝ)*base66 + (28795511111508449/17143750000000000000000000000000 : ℝ)*base67 + (161429414807552199/17143750000000000000000000000000 : ℝ)*base69 + (1476443517929833449/17143750000000000000000000000000 : ℝ)*base71 + (16411287739389/13715000000000000000000000000 : ℝ)*base74 + (42072053550652199/17143750000000000000000000000000 : ℝ)*base75 + (543168934551897801/17143750000000000000000000000000 : ℝ)*base78 + (320896816534545949/17143750000000000000000000000000 : ℝ)*base79 + (25557062415869/13715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (16993621/10000000000000000000000 : ℝ)*base90 + (16993621/10000000000000000000000 : ℝ)*base92 + (16993621/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (636087443986895876317571373/68575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33756373/2000000000000 : ℝ)*(base19) + (919667479/50000000000000 : ℝ)*(base23) + (23414909/12500000000000 : ℝ)*(upper3) + (1338651/2000000000000 : ℝ)*(lower4) + (94453677/50000000000000 : ℝ)*(upper5) + (5941470253905533/100000000000000 : ℝ)*(major0) + (5941470253905533/100000000000000 : ℝ)*(major1) + (5941470253905533/100000000000000 : ℝ)*(major2) + (9344194837/20000000000000 : ℝ)*(sp1) + (50439219549/100000000000000 : ℝ)*(sp2) + (990440931908547/12500000000000 : ℝ)*(sp4) + (7923479046475541/100000000000000 : ℝ)*(sp5) + (7923475176713869/100000000000000 : ℝ)*(sp6) + (1979706371674801/50000000000000 : ℝ)*(sp7) + (1979706371674801/50000000000000 : ℝ)*(f.failure) + (990440931908547/12500000000000 : ℝ)*(f.sum) + (3802065243011/857187500000000000000000000 : ℝ)*base65 + (6846869094990696209/274300000000000000000000000000000 : ℝ)*base67 + (843869517080296209/274300000000000000000000000000000 : ℝ)*base69 + (958653411896796209/274300000000000000000000000000000 : ℝ)*base71 + (95771547717431/13715000000000000000000000000 : ℝ)*base73 + (1877980932798003791/274300000000000000000000000000000 : ℝ)*base76 + (6019575795373496209/274300000000000000000000000000000 : ℝ)*base77 + (6143038881499096209/274300000000000000000000000000000 : ℝ)*base79 + (50397087372969/13715000000000000000000000000 : ℝ)*base82 + (78641819/5000000000000000000000 : ℝ)*base90 + (78641819/5000000000000000000000 : ℝ)*base92 + (78641819/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1172_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_s7_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152617691/10000000000 : ℝ)*x 0 + (2696252739/5000000000 : ℝ)*x 1 + (1316549471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152617691/10000000000 : ℝ)^8365 ≤ (6541566492087/50000000000000 : ℝ)^6317 := by
    have hnat : (2152617691 : ℕ)^8365*50000000000000^6317 ≤ 6541566492087^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152617691 10000000000 6541566492087 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696252739/5000000000 : ℝ)^8365 ≤ (22070181050453/50000000000000 : ℝ)^6317 := by
    have hnat : (2696252739 : ℕ)^8365*50000000000000^6317 ≤ 22070181050453^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696252739 5000000000 22070181050453 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316549471/2500000000 : ℝ)^8365 ≤ (42776504902197/100000000000000 : ℝ)^6317 := by
    have hnat : (1316549471 : ℕ)^8365*100000000000000^6317 ≤ 42776504902197^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316549471 2500000000 42776504902197 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152617691/10000000000 : ℝ), (2696252739/5000000000 : ℝ), (1316549471/2500000000 : ℝ)] ![(6541566492087/50000000000000 : ℝ), (22070181050453/50000000000000 : ℝ), (42776504902197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152617691/10000000000 : ℝ)|^8365 ≤ (6541566492087/50000000000000 : ℝ)^6317
        have hw : |(-2152617691/10000000000 : ℝ)|=(2152617691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696252739/5000000000 : ℝ)|^8365 ≤ (22070181050453/50000000000000 : ℝ)^6317
        have hw : |(2696252739/5000000000 : ℝ)|=(2696252739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316549471/2500000000 : ℝ)|^8365 ≤ (42776504902197/100000000000000 : ℝ)^6317
        have hw : |(1316549471/2500000000 : ℝ)|=(1316549471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s7_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668080629/1250000000 : ℝ)*x 0 + (-1108337929/5000000000 : ℝ)*x 1 + (1316549471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668080629/1250000000 : ℝ)^8365 ≤ (21811168637097/50000000000000 : ℝ)^6317 := by
    have hnat : (668080629 : ℕ)^8365*50000000000000^6317 ≤ 21811168637097^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668080629 1250000000 21811168637097 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108337929/5000000000 : ℝ)^8365 ≤ (6800578902973/50000000000000 : ℝ)^6317 := by
    have hnat : (1108337929 : ℕ)^8365*50000000000000^6317 ≤ 6800578902973^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108337929 5000000000 6800578902973 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316549471/2500000000 : ℝ)^8365 ≤ (42776504902197/100000000000000 : ℝ)^6317 := by
    have hnat : (1316549471 : ℕ)^8365*100000000000000^6317 ≤ 42776504902197^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316549471 2500000000 42776504902197 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668080629/1250000000 : ℝ), (-1108337929/5000000000 : ℝ), (1316549471/2500000000 : ℝ)] ![(21811168637097/50000000000000 : ℝ), (6800578902973/50000000000000 : ℝ), (42776504902197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668080629/1250000000 : ℝ)|^8365 ≤ (21811168637097/50000000000000 : ℝ)^6317
        have hw : |(668080629/1250000000 : ℝ)|=(668080629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1108337929/5000000000 : ℝ)|^8365 ≤ (6800578902973/50000000000000 : ℝ)^6317
        have hw : |(-1108337929/5000000000 : ℝ)|=(1108337929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316549471/2500000000 : ℝ)|^8365 ≤ (42776504902197/100000000000000 : ℝ)^6317
        have hw : |(1316549471/2500000000 : ℝ)|=(1316549471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s7_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668080629/1250000000 : ℝ)*x 0 + (1316549471/2500000000 : ℝ)*x 1 + (-2216675859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668080629/1250000000 : ℝ)^8365 ≤ (21811168637097/50000000000000 : ℝ)^6317 := by
    have hnat : (668080629 : ℕ)^8365*50000000000000^6317 ≤ 21811168637097^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668080629 1250000000 21811168637097 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316549471/2500000000 : ℝ)^8365 ≤ (42776504902197/100000000000000 : ℝ)^6317 := by
    have hnat : (1316549471 : ℕ)^8365*100000000000000^6317 ≤ 42776504902197^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316549471 2500000000 42776504902197 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216675859/10000000000 : ℝ)^8365 ≤ (13601157814071/100000000000000 : ℝ)^6317 := by
    have hnat : (2216675859 : ℕ)^8365*100000000000000^6317 ≤ 13601157814071^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216675859 10000000000 13601157814071 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668080629/1250000000 : ℝ), (1316549471/2500000000 : ℝ), (-2216675859/10000000000 : ℝ)] ![(21811168637097/50000000000000 : ℝ), (42776504902197/100000000000000 : ℝ), (13601157814071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668080629/1250000000 : ℝ)|^8365 ≤ (21811168637097/50000000000000 : ℝ)^6317
        have hw : |(668080629/1250000000 : ℝ)|=(668080629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316549471/2500000000 : ℝ)|^8365 ≤ (42776504902197/100000000000000 : ℝ)^6317
        have hw : |(1316549471/2500000000 : ℝ)|=(1316549471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2216675859/10000000000 : ℝ)|^8365 ≤ (13601157814071/100000000000000 : ℝ)^6317
        have hw : |(-2216675859/10000000000 : ℝ)|=(2216675859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s7_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180231551/5000000000 : ℝ)*x 0 + (4235890323/10000000000 : ℝ)*x 1 + (1122163879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180231551/5000000000 : ℝ)^8365 ≤ (1332684814949/4000000000000 : ℝ)^6317 := by
    have hnat : (2180231551 : ℕ)^8365*4000000000000^6317 ≤ 1332684814949^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180231551 5000000000 1332684814949 4000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235890323/10000000000 : ℝ)^8365 ≤ (16031290942491/50000000000000 : ℝ)^6317 := by
    have hnat : (4235890323 : ℕ)^8365*50000000000000^6317 ≤ 16031290942491^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235890323 10000000000 16031290942491 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122163879/2500000000 : ℝ)^8365 ≤ (34620297725019/100000000000000 : ℝ)^6317 := by
    have hnat : (1122163879 : ℕ)^8365*100000000000000^6317 ≤ 34620297725019^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122163879 2500000000 34620297725019 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180231551/5000000000 : ℝ), (4235890323/10000000000 : ℝ), (1122163879/2500000000 : ℝ)] ![(1332684814949/4000000000000 : ℝ), (16031290942491/50000000000000 : ℝ), (34620297725019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180231551/5000000000 : ℝ)|^8365 ≤ (1332684814949/4000000000000 : ℝ)^6317
        have hw : |(2180231551/5000000000 : ℝ)|=(2180231551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235890323/10000000000 : ℝ)|^8365 ≤ (16031290942491/50000000000000 : ℝ)^6317
        have hw : |(4235890323/10000000000 : ℝ)|=(4235890323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122163879/2500000000 : ℝ)|^8365 ≤ (34620297725019/100000000000000 : ℝ)^6317
        have hw : |(1122163879/2500000000 : ℝ)|=(1122163879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s7_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152622459/10000000000 : ℝ)*x 0 + (329157231/625000000 : ℝ)*x 1 + (674023319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152622459/10000000000 : ℝ)^8365 ≤ (3270792839527/25000000000000 : ℝ)^6317 := by
    have hnat : (2152622459 : ℕ)^8365*25000000000000^6317 ≤ 3270792839527^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152622459 10000000000 3270792839527 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329157231/625000000 : ℝ)^8365 ≤ (42779923419097/100000000000000 : ℝ)^6317 := by
    have hnat : (329157231 : ℕ)^8365*100000000000000^6317 ≤ 42779923419097^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329157231 625000000 42779923419097 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674023319/1250000000 : ℝ)^8365 ≤ (44136905206393/100000000000000 : ℝ)^6317 := by
    have hnat : (674023319 : ℕ)^8365*100000000000000^6317 ≤ 44136905206393^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674023319 1250000000 44136905206393 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152622459/10000000000 : ℝ), (329157231/625000000 : ℝ), (674023319/1250000000 : ℝ)] ![(3270792839527/25000000000000 : ℝ), (42779923419097/100000000000000 : ℝ), (44136905206393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152622459/10000000000 : ℝ)|^8365 ≤ (3270792839527/25000000000000 : ℝ)^6317
        have hw : |(-2152622459/10000000000 : ℝ)|=(2152622459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329157231/625000000 : ℝ)|^8365 ≤ (42779923419097/100000000000000 : ℝ)^6317
        have hw : |(329157231/625000000 : ℝ)|=(329157231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674023319/1250000000 : ℝ)|^8365 ≤ (44136905206393/100000000000000 : ℝ)^6317
        have hw : |(674023319/1250000000 : ℝ)|=(674023319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s7_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212502961/400000000 : ℝ)*x 0 + (-2090687207/10000000000 : ℝ)*x 1 + (2696093307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212502961/400000000 : ℝ)^8365 ≤ (43276051612877/100000000000000 : ℝ)^6317 := by
    have hnat : (212502961 : ℕ)^8365*100000000000000^6317 ≤ 43276051612877^6317*400000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212502961 400000000 43276051612877 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090687207/10000000000 : ℝ)^8365 ≤ (2517408497997/20000000000000 : ℝ)^6317 := by
    have hnat : (2090687207 : ℕ)^8365*20000000000000^6317 ≤ 2517408497997^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090687207 10000000000 2517408497997 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696093307/5000000000 : ℝ)^8365 ≤ (8827381175683/20000000000000 : ℝ)^6317 := by
    have hnat : (2696093307 : ℕ)^8365*20000000000000^6317 ≤ 8827381175683^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696093307 5000000000 8827381175683 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212502961/400000000 : ℝ), (-2090687207/10000000000 : ℝ), (2696093307/5000000000 : ℝ)] ![(43276051612877/100000000000000 : ℝ), (2517408497997/20000000000000 : ℝ), (8827381175683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212502961/400000000 : ℝ)|^8365 ≤ (43276051612877/100000000000000 : ℝ)^6317
        have hw : |(212502961/400000000 : ℝ)|=(212502961/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090687207/10000000000 : ℝ)|^8365 ≤ (2517408497997/20000000000000 : ℝ)^6317
        have hw : |(-2090687207/10000000000 : ℝ)|=(2090687207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696093307/5000000000 : ℝ)|^8365 ≤ (8827381175683/20000000000000 : ℝ)^6317
        have hw : |(2696093307/5000000000 : ℝ)|=(2696093307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s7_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664071751/1250000000 : ℝ)*x 0 + (674023331/1250000000 : ℝ)*x 1 + (-130667949/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664071751/1250000000 : ℝ)^8365 ≤ (43276051429499/100000000000000 : ℝ)^6317 := by
    have hnat : (664071751 : ℕ)^8365*100000000000000^6317 ≤ 43276051429499^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664071751 1250000000 43276051429499 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674023331/1250000000 : ℝ)^8365 ≤ (1379278320217/3125000000000 : ℝ)^6317 := by
    have hnat : (674023331 : ℕ)^8365*3125000000000^6317 ≤ 1379278320217^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674023331 1250000000 1379278320217 3125000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130667949/625000000 : ℝ)^8365 ≤ (12587042306619/100000000000000 : ℝ)^6317 := by
    have hnat : (130667949 : ℕ)^8365*100000000000000^6317 ≤ 12587042306619^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130667949 625000000 12587042306619 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664071751/1250000000 : ℝ), (674023331/1250000000 : ℝ), (-130667949/625000000 : ℝ)] ![(43276051429499/100000000000000 : ℝ), (1379278320217/3125000000000 : ℝ), (12587042306619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664071751/1250000000 : ℝ)|^8365 ≤ (43276051429499/100000000000000 : ℝ)^6317
        have hw : |(664071751/1250000000 : ℝ)|=(664071751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674023331/1250000000 : ℝ)|^8365 ≤ (1379278320217/3125000000000 : ℝ)^6317
        have hw : |(674023331/1250000000 : ℝ)|=(674023331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130667949/625000000 : ℝ)|^8365 ≤ (12587042306619/100000000000000 : ℝ)^6317
        have hw : |(-130667949/625000000 : ℝ)|=(130667949/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s7_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360472749/10000000000 : ℝ)*x 0 + (448801961/1000000000 : ℝ)*x 1 + (4236528523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360472749/10000000000 : ℝ)^8365 ≤ (6663443596207/20000000000000 : ℝ)^6317 := by
    have hnat : (4360472749 : ℕ)^8365*20000000000000^6317 ≤ 6663443596207^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360472749 10000000000 6663443596207 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448801961/1000000000 : ℝ)^8365 ≤ (34613803123063/100000000000000 : ℝ)^6317 := by
    have hnat : (448801961 : ℕ)^8365*100000000000000^6317 ≤ 34613803123063^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448801961 1000000000 34613803123063 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236528523/10000000000 : ℝ)^8365 ≤ (16034489441819/50000000000000 : ℝ)^6317 := by
    have hnat : (4236528523 : ℕ)^8365*50000000000000^6317 ≤ 16034489441819^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236528523 10000000000 16034489441819 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360472749/10000000000 : ℝ), (448801961/1000000000 : ℝ), (4236528523/10000000000 : ℝ)] ![(6663443596207/20000000000000 : ℝ), (34613803123063/100000000000000 : ℝ), (16034489441819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360472749/10000000000 : ℝ)|^8365 ≤ (6663443596207/20000000000000 : ℝ)^6317
        have hw : |(4360472749/10000000000 : ℝ)|=(4360472749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448801961/1000000000 : ℝ)|^8365 ≤ (34613803123063/100000000000000 : ℝ)^6317
        have hw : |(448801961/1000000000 : ℝ)|=(448801961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236528523/10000000000 : ℝ)|^8365 ≤ (16034489441819/50000000000000 : ℝ)^6317
        have hw : |(4236528523/10000000000 : ℝ)|=(4236528523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11391/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5693/50000 : ℝ) ^ (2091/512 : ℝ) ≤ (3500859244278379/25000000000000000000 : ℝ) := by
    have hpowers : (5693/50000 : ℝ)^2091 ≤ (3500859244278379/25000000000000000000 : ℝ)^512 := by
      have hnat : (5693 : ℕ)^2091*25000000000000000000^512 ≤ 3500859244278379^512*50000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5693 50000 3500859244278379 25000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5693/50000 : ℝ)) (X := (3500859244278379/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (33267835004808969/100000000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^2091 ≤ (33267835004808969/100000000000000000000 : ℝ)^512 := by
      have hnat : (14073 : ℕ)^2091*100000000000000000000^512 ≤ 33267835004808969^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 33267835004808969 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (33267835004808969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503500859244278379/12500000000000000000 : ℝ) ≤ (10000685700782897/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (12503500859244278379/12500000000000000000 : ℝ)^512 ≤ (10000685700782897/10000000000000000 : ℝ)^2091 := by
      have hnat : (12503500859244278379 : ℕ)^512*10000000000000000^2091 ≤ 10000685700782897^2091*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503500859244278379 12500000000000000000 10000685700782897 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000685700782897/10000000000000000 : ℝ)) (X := (12503500859244278379/12500000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009454254396384497/20000000000000000000 : ℝ) ≤ (10001157272724007/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (20009454254396384497/20000000000000000000 : ℝ)^512 ≤ (10001157272724007/10000000000000000 : ℝ)^2091 := by
      have hnat : (20009454254396384497 : ℕ)^512*10000000000000000^2091 ≤ 10001157272724007^2091*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009454254396384497 20000000000000000000 10001157272724007 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001157272724007/10000000000000000 : ℝ)) (X := (20009454254396384497/20000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033267835004808969/50000000000000000000 : ℝ) ≤ (10001628844665117/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50033267835004808969/50000000000000000000 : ℝ)^512 ≤ (10001628844665117/10000000000000000 : ℝ)^2091 := by
      have hnat : (50033267835004808969 : ℕ)^512*10000000000000000^2091 ≤ 10001628844665117^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033267835004808969 50000000000000000000 10001628844665117 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001628844665117/10000000000000000 : ℝ)) (X := (50033267835004808969/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3500859244278379/25000000000000000000 : ℝ) ≤ ((26861103841760687319/26870000000000000000 : ℝ)+2*(47157194111/26870000000000 : ℝ)*(5693/50000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (26861103841760687319/26870000000000000000 : ℝ)+2*(47157194111/26870000000000 : ℝ)*(5693/50000 : ℝ)=(10000685700782897/10000000000000000 : ℝ) by norm_num, show 1+2*(3500859244278379/25000000000000000000 : ℝ)=(12503500859244278379/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33267835004808969/100000000000000000000 : ℝ)+(3500859244278379/25000000000000000000 : ℝ) ≤ ((26861103841760687319/26870000000000000000 : ℝ)+(47157194111/26870000000000 : ℝ)*((14073/100000 : ℝ)+(5693/50000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (26861103841760687319/26870000000000000000 : ℝ)+(47157194111/26870000000000 : ℝ)*((14073/100000 : ℝ)+(5693/50000 : ℝ))=(10001157272724007/10000000000000000 : ℝ) by norm_num, show 1+(33267835004808969/100000000000000000000 : ℝ)+(3500859244278379/25000000000000000000 : ℝ)=(20009454254396384497/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33267835004808969/100000000000000000000 : ℝ) ≤ ((26861103841760687319/26870000000000000000 : ℝ)+2*(47157194111/26870000000000 : ℝ)*(14073/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (26861103841760687319/26870000000000000000 : ℝ)+2*(47157194111/26870000000000 : ℝ)*(14073/100000 : ℝ)=(10001628844665117/10000000000000000 : ℝ) by norm_num, show 1+2*(33267835004808969/100000000000000000000 : ℝ)=(50033267835004808969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26861103841760687319/26870000000000000000 : ℝ)*(X 1 0+X 2 0)+(47157194111/26870000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (26861103841760687319/26870000000000000000 : ℝ)) (alpha := (47157194111/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26861103841760687319/26870000000000000000 : ℝ)*(X 0 1+X 2 1)+(47157194111/26870000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (26861103841760687319/26870000000000000000 : ℝ)) (alpha := (47157194111/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26861103841760687319/26870000000000000000 : ℝ)*(X 0 2+X 1 2)+(47157194111/26870000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (26861103841760687319/26870000000000000000 : ℝ)) (alpha := (47157194111/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152617691/10000000000 : ℝ)*X 0 0+(2696252739/5000000000 : ℝ)*X 0 1+(1316549471/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668080629/1250000000 : ℝ)*X 1 0+(-1108337929/5000000000 : ℝ)*X 1 1+(1316549471/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668080629/1250000000 : ℝ)*X 2 0+(1316549471/2500000000 : ℝ)*X 2 1+(-2216675859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180231551/5000000000 : ℝ)*X 0 0+(4235890323/10000000000 : ℝ)*X 0 1+(1122163879/2500000000 : ℝ)*X 0 2+(2180231551/5000000000 : ℝ)*X 1 0+(4235890323/10000000000 : ℝ)*X 1 1+(1122163879/2500000000 : ℝ)*X 1 2+(2180231551/5000000000 : ℝ)*X 2 0+(4235890323/10000000000 : ℝ)*X 2 1+(1122163879/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2152622459/10000000000 : ℝ)*X 0 0+(329157231/625000000 : ℝ)*X 0 1+(674023319/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212502961/400000000 : ℝ)*X 1 0+(-2090687207/10000000000 : ℝ)*X 1 1+(2696093307/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664071751/1250000000 : ℝ)*X 2 0+(674023331/1250000000 : ℝ)*X 2 1+(-130667949/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360472749/10000000000 : ℝ)*X 0 0+(448801961/1000000000 : ℝ)*X 0 1+(4236528523/10000000000 : ℝ)*X 0 2+(4360472749/10000000000 : ℝ)*X 1 0+(448801961/1000000000 : ℝ)*X 1 1+(4236528523/10000000000 : ℝ)*X 1 2+(4360472749/10000000000 : ℝ)*X 2 0+(448801961/1000000000 : ℝ)*X 2 1+(4236528523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12759011518671508662339252537/1343500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (465965537/25000000000000 : ℝ)*(base19) + (867772647/50000000000000 : ℝ)*(base23) + (34290401/50000000000000 : ℝ)*(lower2) + (9581157/4000000000000 : ℝ)*(upper3) + (17987733/12500000000000 : ℝ)*(upper5) + (5936789256685353/100000000000000 : ℝ)*(major0) + (5936789256685353/100000000000000 : ℝ)*(major1) + (5936789256685353/100000000000000 : ℝ)*(major2) + (7917233863981119/100000000000000 : ℝ)*(sp0) + (989660377438971/12500000000000 : ℝ)*(sp1) + (7917283147828623/100000000000000 : ℝ)*(sp2) + (989066433624887/25000000000000 : ℝ)*(sp3) + (51019392799/100000000000000 : ℝ)*(sp4) + (27578935719/100000000000000 : ℝ)*(sp7) + (989073328358817/25000000000000 : ℝ)*(f.failure) + (7917284883373917/100000000000000 : ℝ)*(f.sum) + (11373066134407/2687000000000000000000000000 : ℝ)*base65 + (26474098812723138607/2687000000000000000000000000000000 : ℝ)*base67 + (21716645824520138607/2687000000000000000000000000000000 : ℝ)*base69 + (75720173473122138607/2687000000000000000000000000000000 : ℝ)*base71 + (209972312023/335875000000000000000000000 : ℝ)*base74 + (78983312720604138607/2687000000000000000000000000000000 : ℝ)*base75 + (17687383687802138607/2687000000000000000000000000000000 : ℝ)*base77 + (63505551578221138607/2687000000000000000000000000000000 : ℝ)*base79 + (1193422676219/268700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (87723/2500000000000000000000 : ℝ)*base90 + (87723/2500000000000000000000 : ℝ)*base92 + (87723/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2772298366812639261782256321/335875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1101399873/100000000000000 : ℝ)*(base19) + (263481517/20000000000000 : ℝ)*(base23) + (167240163/100000000000000 : ℝ)*(upper3) + (101547803/100000000000000 : ℝ)*(lower4) + (65251021/50000000000000 : ℝ)*(upper5) + (1491696739101853/25000000000000 : ℝ)*(major0) + (1491696739101853/25000000000000 : ℝ)*(major1) + (1491696739101853/25000000000000 : ℝ)*(major2) + (30923364521/100000000000000 : ℝ)*(sp1) + (39259621721/100000000000000 : ℝ)*(sp2) + (318291590859719/4000000000000 : ℝ)*(sp4) + (7957257746728581/100000000000000 : ℝ)*(sp5) + (795724919446367/10000000000000 : ℝ)*(sp6) + (3976283866189887/100000000000000 : ℝ)*(sp7) + (3976283866189887/100000000000000 : ℝ)*(f.failure) + (318291590859719/4000000000000 : ℝ)*(f.sum) + (4364236465621/1343500000000000000000000000 : ℝ)*base66 + (1964111628387002107/671750000000000000000000000000000 : ℝ)*base67 + (1740790764387247893/671750000000000000000000000000000 : ℝ)*base70 + (4159083011720497893/671750000000000000000000000000000 : ℝ)*base72 + (2898013289831/2687000000000000000000000000 : ℝ)*base74 + (4538180021781252107/671750000000000000000000000000000 : ℝ)*base75 + (5536715458831747893/671750000000000000000000000000000 : ℝ)*base78 + (7759120932309997893/671750000000000000000000000000000 : ℝ)*base80 + (1355740005227/268700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (71679947/10000000000000000000000 : ℝ)*base89 + (71679947/10000000000000000000000 : ℝ)*base91 + (71679947/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1172_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_s8_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152624721/10000000000 : ℝ)*x 0 + (5392450119/10000000000 : ℝ)*x 1 + (5266248409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152624721/10000000000 : ℝ)^8365 ≤ (13083189563201/100000000000000 : ℝ)^6317 := by
    have hnat : (2152624721 : ℕ)^8365*100000000000000^6317 ≤ 13083189563201^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152624721 10000000000 13083189563201 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392450119/10000000000 : ℝ)^8365 ≤ (441397620503/1000000000000 : ℝ)^6317 := by
    have hnat : (5392450119 : ℕ)^8365*1000000000000^6317 ≤ 441397620503^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392450119 10000000000 441397620503 1000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266248409/10000000000 : ℝ)^8365 ≤ (2673565522841/6250000000000 : ℝ)^6317 := by
    have hnat : (5266248409 : ℕ)^8365*6250000000000^6317 ≤ 2673565522841^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266248409 10000000000 2673565522841 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152624721/10000000000 : ℝ), (5392450119/10000000000 : ℝ), (5266248409/10000000000 : ℝ)] ![(13083189563201/100000000000000 : ℝ), (441397620503/1000000000000 : ℝ), (2673565522841/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152624721/10000000000 : ℝ)|^8365 ≤ (13083189563201/100000000000000 : ℝ)^6317
        have hw : |(-2152624721/10000000000 : ℝ)|=(2152624721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392450119/10000000000 : ℝ)|^8365 ≤ (441397620503/1000000000000 : ℝ)^6317
        have hw : |(5392450119/10000000000 : ℝ)|=(5392450119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266248409/10000000000 : ℝ)|^8365 ≤ (2673565522841/6250000000000 : ℝ)^6317
        have hw : |(5266248409/10000000000 : ℝ)|=(5266248409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s8_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344630397/10000000000 : ℝ)*x 0 + (-2216628523/10000000000 : ℝ)*x 1 + (2633124173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344630397/10000000000 : ℝ)^8365 ≤ (21811089549629/50000000000000 : ℝ)^6317 := by
    have hnat : (5344630397 : ℕ)^8365*50000000000000^6317 ≤ 21811089549629^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344630397 10000000000 21811089549629 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216628523/10000000000 : ℝ)^8365 ≤ (106256040669/781250000000 : ℝ)^6317 := by
    have hnat : (2216628523 : ℕ)^8365*781250000000^6317 ≤ 106256040669^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216628523 10000000000 106256040669 781250000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633124173/5000000000 : ℝ)^8365 ≤ (21388523843903/50000000000000 : ℝ)^6317 := by
    have hnat : (2633124173 : ℕ)^8365*50000000000000^6317 ≤ 21388523843903^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633124173 5000000000 21388523843903 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344630397/10000000000 : ℝ), (-2216628523/10000000000 : ℝ), (2633124173/5000000000 : ℝ)] ![(21811089549629/50000000000000 : ℝ), (106256040669/781250000000 : ℝ), (21388523843903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344630397/10000000000 : ℝ)|^8365 ≤ (21811089549629/50000000000000 : ℝ)^6317
        have hw : |(5344630397/10000000000 : ℝ)|=(5344630397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216628523/10000000000 : ℝ)|^8365 ≤ (106256040669/781250000000 : ℝ)^6317
        have hw : |(-2216628523/10000000000 : ℝ)|=(2216628523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633124173/5000000000 : ℝ)|^8365 ≤ (21388523843903/50000000000000 : ℝ)^6317
        have hw : |(2633124173/5000000000 : ℝ)|=(2633124173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s8_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068926079/2000000000 : ℝ)*x 0 + (1053249681/2000000000 : ℝ)*x 1 + (-2216628447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068926079/2000000000 : ℝ)^8365 ≤ (21811089538821/50000000000000 : ℝ)^6317 := by
    have hnat : (1068926079 : ℕ)^8365*50000000000000^6317 ≤ 21811089538821^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068926079 2000000000 21811089538821 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053249681/2000000000 : ℝ)^8365 ≤ (4277704832243/10000000000000 : ℝ)^6317 := by
    have hnat : (1053249681 : ℕ)^8365*10000000000000^6317 ≤ 4277704832243^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053249681 2000000000 4277704832243 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216628447/10000000000 : ℝ)^8365 ≤ (13600772588129/100000000000000 : ℝ)^6317 := by
    have hnat : (2216628447 : ℕ)^8365*100000000000000^6317 ≤ 13600772588129^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216628447 10000000000 13600772588129 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068926079/2000000000 : ℝ), (1053249681/2000000000 : ℝ), (-2216628447/10000000000 : ℝ)] ![(21811089538821/50000000000000 : ℝ), (4277704832243/10000000000000 : ℝ), (13600772588129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068926079/2000000000 : ℝ)|^8365 ≤ (21811089538821/50000000000000 : ℝ)^6317
        have hw : |(1068926079/2000000000 : ℝ)|=(1068926079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053249681/2000000000 : ℝ)|^8365 ≤ (4277704832243/10000000000000 : ℝ)^6317
        have hw : |(1053249681/2000000000 : ℝ)|=(1053249681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2216628447/10000000000 : ℝ)|^8365 ≤ (13600772588129/100000000000000 : ℝ)^6317
        have hw : |(-2216628447/10000000000 : ℝ)|=(2216628447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s8_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360465821/10000000000 : ℝ)*x 0 + (84719917/200000000 : ℝ)*x 1 + (4488549259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360465821/10000000000 : ℝ)^8365 ≤ (8329286971067/25000000000000 : ℝ)^6317 := by
    have hnat : (4360465821 : ℕ)^8365*25000000000000^6317 ≤ 8329286971067^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360465821 10000000000 8329286971067 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84719917/200000000 : ℝ)^8365 ≤ (4007954951683/12500000000000 : ℝ)^6317 := by
    have hnat : (84719917 : ℕ)^8365*12500000000000^6317 ≤ 4007954951683^6317*200000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84719917 200000000 4007954951683 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488549259/10000000000 : ℝ)^8365 ≤ (4327401560727/12500000000000 : ℝ)^6317 := by
    have hnat : (4488549259 : ℕ)^8365*12500000000000^6317 ≤ 4327401560727^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488549259 10000000000 4327401560727 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360465821/10000000000 : ℝ), (84719917/200000000 : ℝ), (4488549259/10000000000 : ℝ)] ![(8329286971067/25000000000000 : ℝ), (4007954951683/12500000000000 : ℝ), (4327401560727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360465821/10000000000 : ℝ)|^8365 ≤ (8329286971067/25000000000000 : ℝ)^6317
        have hw : |(4360465821/10000000000 : ℝ)|=(4360465821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84719917/200000000 : ℝ)|^8365 ≤ (4007954951683/12500000000000 : ℝ)^6317
        have hw : |(84719917/200000000 : ℝ)|=(84719917/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488549259/10000000000 : ℝ)|^8365 ≤ (4327401560727/12500000000000 : ℝ)^6317
        have hw : |(4488549259/10000000000 : ℝ)|=(4488549259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s8_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152629539/10000000000 : ℝ)*x 0 + (2633282807/5000000000 : ℝ)*x 1 + (2696065879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152629539/10000000000 : ℝ)^8365 ≤ (13083228339587/100000000000000 : ℝ)^6317 := by
    have hnat : (2152629539 : ℕ)^8365*100000000000000^6317 ≤ 13083228339587^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152629539 10000000000 13083228339587 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633282807/5000000000 : ℝ)^8365 ≤ (21390230181881/50000000000000 : ℝ)^6317 := by
    have hnat : (2633282807 : ℕ)^8365*50000000000000^6317 ≤ 21390230181881^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633282807 5000000000 21390230181881 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696065879/5000000000 : ℝ)^8365 ≤ (44136311291347/100000000000000 : ℝ)^6317 := by
    have hnat : (2696065879 : ℕ)^8365*100000000000000^6317 ≤ 44136311291347^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696065879 5000000000 44136311291347 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152629539/10000000000 : ℝ), (2633282807/5000000000 : ℝ), (2696065879/5000000000 : ℝ)] ![(13083228339587/100000000000000 : ℝ), (21390230181881/50000000000000 : ℝ), (44136311291347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152629539/10000000000 : ℝ)|^8365 ≤ (13083228339587/100000000000000 : ℝ)^6317
        have hw : |(-2152629539/10000000000 : ℝ)|=(2152629539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633282807/5000000000 : ℝ)|^8365 ≤ (21390230181881/50000000000000 : ℝ)^6317
        have hw : |(2633282807/5000000000 : ℝ)|=(2633282807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696065879/5000000000 : ℝ)|^8365 ≤ (44136311291347/100000000000000 : ℝ)^6317
        have hw : |(2696065879/5000000000 : ℝ)|=(2696065879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s8_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328146591/2500000000 : ℝ)*x 0 + (-2090745093/10000000000 : ℝ)*x 1 + (2696065879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328146591/2500000000 : ℝ)^8365 ≤ (5409523089101/12500000000000 : ℝ)^6317 := by
    have hnat : (1328146591 : ℕ)^8365*12500000000000^6317 ≤ 5409523089101^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328146591 2500000000 5409523089101 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090745093/10000000000 : ℝ)^8365 ≤ (6293751991533/50000000000000 : ℝ)^6317 := by
    have hnat : (2090745093 : ℕ)^8365*50000000000000^6317 ≤ 6293751991533^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090745093 10000000000 6293751991533 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696065879/5000000000 : ℝ)^8365 ≤ (44136311291347/100000000000000 : ℝ)^6317 := by
    have hnat : (2696065879 : ℕ)^8365*100000000000000^6317 ≤ 44136311291347^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696065879 5000000000 44136311291347 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328146591/2500000000 : ℝ), (-2090745093/10000000000 : ℝ), (2696065879/5000000000 : ℝ)] ![(5409523089101/12500000000000 : ℝ), (6293751991533/50000000000000 : ℝ), (44136311291347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328146591/2500000000 : ℝ)|^8365 ≤ (5409523089101/12500000000000 : ℝ)^6317
        have hw : |(1328146591/2500000000 : ℝ)|=(1328146591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090745093/10000000000 : ℝ)|^8365 ≤ (6293751991533/50000000000000 : ℝ)^6317
        have hw : |(-2090745093/10000000000 : ℝ)|=(2090745093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696065879/5000000000 : ℝ)|^8365 ≤ (44136311291347/100000000000000 : ℝ)^6317
        have hw : |(2696065879/5000000000 : ℝ)|=(2696065879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s8_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062517273/2000000000 : ℝ)*x 0 + (5392131757/10000000000 : ℝ)*x 1 + (-2090745093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062517273/2000000000 : ℝ)^8365 ≤ (8655236944719/20000000000000 : ℝ)^6317 := by
    have hnat : (1062517273 : ℕ)^8365*20000000000000^6317 ≤ 8655236944719^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062517273 2000000000 8655236944719 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392131757/10000000000 : ℝ)^8365 ≤ (11034077820127/25000000000000 : ℝ)^6317 := by
    have hnat : (5392131757 : ℕ)^8365*25000000000000^6317 ≤ 11034077820127^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392131757 10000000000 11034077820127 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090745093/10000000000 : ℝ)^8365 ≤ (6293751991533/50000000000000 : ℝ)^6317 := by
    have hnat : (2090745093 : ℕ)^8365*50000000000000^6317 ≤ 6293751991533^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090745093 10000000000 6293751991533 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062517273/2000000000 : ℝ), (5392131757/10000000000 : ℝ), (-2090745093/10000000000 : ℝ)] ![(8655236944719/20000000000000 : ℝ), (11034077820127/25000000000000 : ℝ), (6293751991533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062517273/2000000000 : ℝ)|^8365 ≤ (8655236944719/20000000000000 : ℝ)^6317
        have hw : |(1062517273/2000000000 : ℝ)|=(1062517273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392131757/10000000000 : ℝ)|^8365 ≤ (11034077820127/25000000000000 : ℝ)^6317
        have hw : |(5392131757/10000000000 : ℝ)|=(5392131757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090745093/10000000000 : ℝ)|^8365 ≤ (6293751991533/50000000000000 : ℝ)^6317
        have hw : |(-2090745093/10000000000 : ℝ)|=(2090745093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s8_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360475401/10000000000 : ℝ)*x 0 + (2243957213/5000000000 : ℝ)*x 1 + (4236633013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360475401/10000000000 : ℝ)^8365 ≤ (33317244813699/100000000000000 : ℝ)^6317 := by
    have hnat : (4360475401 : ℕ)^8365*100000000000000^6317 ≤ 33317244813699^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360475401 10000000000 33317244813699 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243957213/5000000000 : ℝ)^8365 ≤ (432659111151/1250000000000 : ℝ)^6317 := by
    have hnat : (2243957213 : ℕ)^8365*1250000000000^6317 ≤ 432659111151^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243957213 5000000000 432659111151 1250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236633013/10000000000 : ℝ)^8365 ≤ (1282801050763/4000000000000 : ℝ)^6317 := by
    have hnat : (4236633013 : ℕ)^8365*4000000000000^6317 ≤ 1282801050763^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236633013 10000000000 1282801050763 4000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360475401/10000000000 : ℝ), (2243957213/5000000000 : ℝ), (4236633013/10000000000 : ℝ)] ![(33317244813699/100000000000000 : ℝ), (432659111151/1250000000000 : ℝ), (1282801050763/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360475401/10000000000 : ℝ)|^8365 ≤ (33317244813699/100000000000000 : ℝ)^6317
        have hw : |(4360475401/10000000000 : ℝ)|=(4360475401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243957213/5000000000 : ℝ)|^8365 ≤ (432659111151/1250000000000 : ℝ)^6317
        have hw : |(2243957213/5000000000 : ℝ)|=(2243957213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236633013/10000000000 : ℝ)|^8365 ≤ (1282801050763/4000000000000 : ℝ)^6317
        have hw : |(4236633013/10000000000 : ℝ)|=(4236633013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (356/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11391/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (7014284041728261/50000000000000000000 : ℝ) := by
    have hpowers : (11391/100000 : ℝ)^2091 ≤ (7014284041728261/50000000000000000000 : ℝ)^512 := by
      have hnat : (11391 : ℕ)^2091*50000000000000000000^512 ≤ 7014284041728261^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11391 100000 7014284041728261 50000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11391/100000 : ℝ)) (X := (7014284041728261/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14067/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (33209947124426667/100000000000000000000 : ℝ) := by
    have hpowers : (14067/100000 : ℝ)^2091 ≤ (33209947124426667/100000000000000000000 : ℝ)^512 := by
      have hnat : (14067 : ℕ)^2091*100000000000000000000^512 ≤ 33209947124426667^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14067 100000 33209947124426667 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14067/100000 : ℝ)) (X := (33209947124426667/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007014284041728261/25000000000000000000 : ℝ) ≤ (200013738624751/200000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (25007014284041728261/25000000000000000000 : ℝ)^512 ≤ (200013738624751/200000000000000 : ℝ)^2091 := by
      have hnat : (25007014284041728261 : ℕ)^512*200000000000000^2091 ≤ 200013738624751^2091*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007014284041728261 25000000000000000000 200013738624751 200000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013738624751/200000000000000 : ℝ)) (X := (25007014284041728261/25000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047238515207883189/100000000000000000000 : ℝ) ≤ (400046258837251/400000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (100047238515207883189/100000000000000000000 : ℝ)^512 ≤ (400046258837251/400000000000000 : ℝ)^2091 := by
      have hnat : (100047238515207883189 : ℕ)^512*400000000000000^2091 ≤ 400046258837251^2091*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047238515207883189 100000000000000000000 400046258837251 400000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400046258837251/400000000000000 : ℝ)) (X := (100047238515207883189/100000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033209947124426667/50000000000000000000 : ℝ) ≤ (16002601617/16000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50033209947124426667/50000000000000000000 : ℝ)^512 ≤ (16002601617/16000000000 : ℝ)^2091 := by
      have hnat : (50033209947124426667 : ℕ)^512*16000000000^2091 ≤ 16002601617^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033209947124426667 50000000000000000000 16002601617 16000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16002601617/16000000000 : ℝ)) (X := (50033209947124426667/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7014284041728261/50000000000000000000 : ℝ) ≤ ((178340941164594939/178400000000000000 : ℝ)+2*(18781587749/10704000000000 : ℝ)*(11391/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (178340941164594939/178400000000000000 : ℝ)+2*(18781587749/10704000000000 : ℝ)*(11391/100000 : ℝ)=(200013738624751/200000000000000 : ℝ) by norm_num, show 1+2*(7014284041728261/50000000000000000000 : ℝ)=(25007014284041728261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33209947124426667/100000000000000000000 : ℝ)+(7014284041728261/50000000000000000000 : ℝ) ≤ ((178340941164594939/178400000000000000 : ℝ)+(18781587749/10704000000000 : ℝ)*((14067/100000 : ℝ)+(11391/100000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (178340941164594939/178400000000000000 : ℝ)+(18781587749/10704000000000 : ℝ)*((14067/100000 : ℝ)+(11391/100000 : ℝ))=(400046258837251/400000000000000 : ℝ) by norm_num, show 1+(33209947124426667/100000000000000000000 : ℝ)+(7014284041728261/50000000000000000000 : ℝ)=(100047238515207883189/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33209947124426667/100000000000000000000 : ℝ) ≤ ((178340941164594939/178400000000000000 : ℝ)+2*(18781587749/10704000000000 : ℝ)*(14067/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (178340941164594939/178400000000000000 : ℝ)+2*(18781587749/10704000000000 : ℝ)*(14067/100000 : ℝ)=(16002601617/16000000000 : ℝ) by norm_num, show 1+2*(33209947124426667/100000000000000000000 : ℝ)=(50033209947124426667/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (178340941164594939/178400000000000000 : ℝ)*(X 1 0+X 2 0)+(18781587749/10704000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (178340941164594939/178400000000000000 : ℝ)) (alpha := (18781587749/10704000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (178340941164594939/178400000000000000 : ℝ)*(X 0 1+X 2 1)+(18781587749/10704000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (178340941164594939/178400000000000000 : ℝ)) (alpha := (18781587749/10704000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (178340941164594939/178400000000000000 : ℝ)*(X 0 2+X 1 2)+(18781587749/10704000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (178340941164594939/178400000000000000 : ℝ)) (alpha := (18781587749/10704000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152624721/10000000000 : ℝ)*X 0 0+(5392450119/10000000000 : ℝ)*X 0 1+(5266248409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344630397/10000000000 : ℝ)*X 1 0+(-2216628523/10000000000 : ℝ)*X 1 1+(2633124173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068926079/2000000000 : ℝ)*X 2 0+(1053249681/2000000000 : ℝ)*X 2 1+(-2216628447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360465821/10000000000 : ℝ)*X 0 0+(84719917/200000000 : ℝ)*X 0 1+(4488549259/10000000000 : ℝ)*X 0 2+(4360465821/10000000000 : ℝ)*X 1 0+(84719917/200000000 : ℝ)*X 1 1+(4488549259/10000000000 : ℝ)*X 1 2+(4360465821/10000000000 : ℝ)*X 2 0+(84719917/200000000 : ℝ)*X 2 1+(4488549259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2152629539/10000000000 : ℝ)*X 0 0+(2633282807/5000000000 : ℝ)*X 0 1+(2696065879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328146591/2500000000 : ℝ)*X 1 0+(-2090745093/10000000000 : ℝ)*X 1 1+(2696065879/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062517273/2000000000 : ℝ)*X 2 0+(5392131757/10000000000 : ℝ)*X 2 1+(-2090745093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360475401/10000000000 : ℝ)*X 0 0+(2243957213/5000000000 : ℝ)*X 0 1+(4236633013/10000000000 : ℝ)*X 0 2+(4360475401/10000000000 : ℝ)*X 1 0+(2243957213/5000000000 : ℝ)*X 1 1+(4236633013/10000000000 : ℝ)*X 1 2+(4360475401/10000000000 : ℝ)*X 2 0+(2243957213/5000000000 : ℝ)*X 2 1+(4236633013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9194823735928836873569/892000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252320269/12500000000000 : ℝ)*(base19) + (915878749/50000000000000 : ℝ)*(base23) + (19651079/20000000000000 : ℝ)*(lower2) + (54428611/25000000000000 : ℝ)*(upper3) + (204132889/100000000000000 : ℝ)*(upper5) + (5941771898133379/100000000000000 : ℝ)*(major0) + (5941771898133379/100000000000000 : ℝ)*(major1) + (5941771898133379/100000000000000 : ℝ)*(major2) + (7923875046751621/100000000000000 : ℝ)*(sp0) + (3961963837088461/50000000000000 : ℝ)*(sp1) + (990490982622697/12500000000000 : ℝ)*(sp2) + (1979792711281177/50000000000000 : ℝ)*(sp3) + (13661496863/25000000000000 : ℝ)*(sp4) + (5667472409/20000000000000 : ℝ)*(sp7) + (3959613759924399/100000000000000 : ℝ)*(f.failure) + (3961964846369537/50000000000000 : ℝ)*(f.sum) + (715742679959/535200000000000000000000000 : ℝ)*base65 + (134037155085216643/53520000000000000000000000000000 : ℝ)*base67 + (105342493841136643/53520000000000000000000000000000 : ℝ)*base69 + (719273259124896643/53520000000000000000000000000000 : ℝ)*base71 + (2830722862709/2676000000000000000000000000 : ℝ)*base74 + (455854814421503357/53520000000000000000000000000000 : ℝ)*base76 + (690845180965823357/53520000000000000000000000000000 : ℝ)*base78 + (365883416407343357/53520000000000000000000000000000 : ℝ)*base80 + (8390684587231/2676000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (20737019/10000000000000000000000 : ℝ)*base89 + (20737019/10000000000000000000000 : ℝ)*base91 + (20737019/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20080050068021028663995657/2230000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1634181949/100000000000000 : ℝ)*(base19) + (444354621/25000000000000 : ℝ)*(base23) + (286082641/50000000000000 : ℝ)*(lower1) + (90422119/50000000000000 : ℝ)*(upper3) + (64460649/100000000000000 : ℝ)*(lower4) + (183929871/100000000000000 : ℝ)*(upper5) + (1492932734610493/25000000000000 : ℝ)*(major0) + (1492932734610493/25000000000000 : ℝ)*(major1) + (1492932734610493/25000000000000 : ℝ)*(major2) + (676482857/20000000000000 : ℝ)*(sp2) + (7963883026798197/100000000000000 : ℝ)*(sp4) + (995485174077031/12500000000000 : ℝ)*(sp5) + (7963877866965429/100000000000000 : ℝ)*(sp6) + (397957854993549/10000000000000 : ℝ)*(sp7) + (397957854993549/10000000000000 : ℝ)*(f.failure) + (7963883026798197/100000000000000 : ℝ)*(f.sum) + (1109840007049/334500000000000000000000000 : ℝ)*base66 + (795204569145894781/13380000000000000000000000000000 : ℝ)*base67 + (91253400072654781/13380000000000000000000000000000 : ℝ)*base69 + (1407546329429574781/13380000000000000000000000000000 : ℝ)*base71 + (2346534416041/669000000000000000000000000 : ℝ)*base73 + (1369755702328614781/13380000000000000000000000000000 : ℝ)*base75 + (86735269048134781/13380000000000000000000000000000 : ℝ)*base77 + (132558781722294781/13380000000000000000000000000000 : ℝ)*base79 + (5825690055103/669000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1933169/1000000000000000000000 : ℝ)*base89 + (1933169/1000000000000000000000 : ℝ)*base91 + (1933169/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1172_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1172_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1172_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1172_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1172_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
