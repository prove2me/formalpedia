-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1055_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:58:41.011483+00:00
-- url     : https://prove2.me/submissions/3f94cc91-4f39-4392-bd63-deade8034481

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
theorem support_rectangle_w1055_s9_0 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-276149851/1250000000 : ℝ)*x 0 + (539452237/1000000000 : ℝ)*x 1 + (2632136633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276149851/1250000000 : ℝ)^1031 ≤ (134159288737/1000000000000 : ℝ)^775 := by
    have hnat : (276149851 : ℕ)^1031*1000000000000^775 ≤ 134159288737^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276149851 1250000000 134159288737 1000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539452237/1000000000 : ℝ)^1031 ≤ (8799155986961/20000000000000 : ℝ)^775 := by
    have hnat : (539452237 : ℕ)^1031*20000000000000^775 ≤ 8799155986961^775*1000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539452237 1000000000 8799155986961 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632136633/5000000000 : ℝ)^1031 ≤ (10647072794821/25000000000000 : ℝ)^775 := by
    have hnat : (2632136633 : ℕ)^1031*25000000000000^775 ≤ 10647072794821^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632136633 5000000000 10647072794821 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276149851/1250000000 : ℝ), (539452237/1000000000 : ℝ), (2632136633/5000000000 : ℝ)] ![(134159288737/1000000000000 : ℝ), (8799155986961/20000000000000 : ℝ), (10647072794821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276149851/1250000000 : ℝ)|^1031 ≤ (134159288737/1000000000000 : ℝ)^775
        have hw : |(-276149851/1250000000 : ℝ)|=(276149851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539452237/1000000000 : ℝ)|^1031 ≤ (8799155986961/20000000000000 : ℝ)^775
        have hw : |(539452237/1000000000 : ℝ)|=(539452237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632136633/5000000000 : ℝ)|^1031 ≤ (10647072794821/25000000000000 : ℝ)^775
        have hw : |(2632136633/5000000000 : ℝ)|=(2632136633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s9_1 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672498307/5000000000 : ℝ)*x 0 + (-1137643031/5000000000 : ℝ)*x 1 + (5264273121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672498307/5000000000 : ℝ)^1031 ≤ (21729630088457/50000000000000 : ℝ)^775 := by
    have hnat : (2672498307 : ℕ)^1031*50000000000000^775 ≤ 21729630088457^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672498307 5000000000 21729630088457 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137643031/5000000000 : ℝ)^1031 ≤ (13952450190839/100000000000000 : ℝ)^775 := by
    have hnat : (1137643031 : ℕ)^1031*100000000000000^775 ≤ 13952450190839^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137643031 5000000000 13952450190839 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264273121/10000000000 : ℝ)^1031 ≤ (42588289618737/100000000000000 : ℝ)^775 := by
    have hnat : (5264273121 : ℕ)^1031*100000000000000^775 ≤ 42588289618737^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264273121 10000000000 42588289618737 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672498307/5000000000 : ℝ), (-1137643031/5000000000 : ℝ), (5264273121/10000000000 : ℝ)] ![(21729630088457/50000000000000 : ℝ), (13952450190839/100000000000000 : ℝ), (42588289618737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672498307/5000000000 : ℝ)|^1031 ≤ (21729630088457/50000000000000 : ℝ)^775
        have hw : |(2672498307/5000000000 : ℝ)|=(2672498307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1137643031/5000000000 : ℝ)|^1031 ≤ (13952450190839/100000000000000 : ℝ)^775
        have hw : |(-1137643031/5000000000 : ℝ)|=(1137643031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264273121/10000000000 : ℝ)|^1031 ≤ (42588289618737/100000000000000 : ℝ)^775
        have hw : |(5264273121/10000000000 : ℝ)|=(5264273121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s9_2 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1068999317/2000000000 : ℝ)*x 0 + (5264273193/10000000000 : ℝ)*x 1 + (-568821501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068999317/2000000000 : ℝ)^1031 ≤ (43459259863231/100000000000000 : ℝ)^775 := by
    have hnat : (1068999317 : ℕ)^1031*100000000000000^775 ≤ 43459259863231^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068999317 2000000000 43459259863231 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264273193/10000000000 : ℝ)^1031 ≤ (4258829039363/10000000000000 : ℝ)^775 := by
    have hnat : (5264273193 : ℕ)^1031*10000000000000^775 ≤ 4258829039363^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264273193 10000000000 4258829039363 10000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568821501/2500000000 : ℝ)^1031 ≤ (13952449717689/100000000000000 : ℝ)^775 := by
    have hnat : (568821501 : ℕ)^1031*100000000000000^775 ≤ 13952449717689^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568821501 2500000000 13952449717689 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068999317/2000000000 : ℝ), (5264273193/10000000000 : ℝ), (-568821501/2500000000 : ℝ)] ![(43459259863231/100000000000000 : ℝ), (4258829039363/10000000000000 : ℝ), (13952449717689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068999317/2000000000 : ℝ)|^1031 ≤ (43459259863231/100000000000000 : ℝ)^775
        have hw : |(1068999317/2000000000 : ℝ)|=(1068999317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264273193/10000000000 : ℝ)|^1031 ≤ (4258829039363/10000000000000 : ℝ)^775
        have hw : |(5264273193/10000000000 : ℝ)|=(5264273193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-568821501/2500000000 : ℝ)|^1031 ≤ (13952449717689/100000000000000 : ℝ)^775
        have hw : |(-568821501/2500000000 : ℝ)|=(568821501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s9_3 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2188538873/5000000000 : ℝ)*x 0 + (850320647/2000000000 : ℝ)*x 1 + (4506316599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188538873/5000000000 : ℝ)^1031 ≤ (33316496048257/100000000000000 : ℝ)^775 := by
    have hnat : (2188538873 : ℕ)^1031*100000000000000^775 ≤ 33316496048257^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188538873 5000000000 33316496048257 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850320647/2000000000 : ℝ)^1031 ≤ (32052012810329/100000000000000 : ℝ)^775 := by
    have hnat : (850320647 : ℕ)^1031*100000000000000^775 ≤ 32052012810329^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850320647 2000000000 32052012810329 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506316599/10000000000 : ℝ)^1031 ≤ (8657872781239/25000000000000 : ℝ)^775 := by
    have hnat : (4506316599 : ℕ)^1031*25000000000000^775 ≤ 8657872781239^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506316599 10000000000 8657872781239 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188538873/5000000000 : ℝ), (850320647/2000000000 : ℝ), (4506316599/10000000000 : ℝ)] ![(33316496048257/100000000000000 : ℝ), (32052012810329/100000000000000 : ℝ), (8657872781239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188538873/5000000000 : ℝ)|^1031 ≤ (33316496048257/100000000000000 : ℝ)^775
        have hw : |(2188538873/5000000000 : ℝ)|=(2188538873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850320647/2000000000 : ℝ)|^1031 ≤ (32052012810329/100000000000000 : ℝ)^775
        have hw : |(850320647/2000000000 : ℝ)|=(850320647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506316599/10000000000 : ℝ)|^1031 ≤ (8657872781239/25000000000000 : ℝ)^775
        have hw : |(4506316599/10000000000 : ℝ)|=(4506316599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s9_4 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209204427/10000000000 : ℝ)*x 0 + (658074907/1250000000 : ℝ)*x 1 + (539419481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209204427/10000000000 : ℝ)^1031 ≤ (3353993567021/25000000000000 : ℝ)^775 := by
    have hnat : (2209204427 : ℕ)^1031*25000000000000^775 ≤ 3353993567021^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209204427 10000000000 3353993567021 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658074907/1250000000 : ℝ)^1031 ≤ (21295899823449/50000000000000 : ℝ)^775 := by
    have hnat : (658074907 : ℕ)^1031*50000000000000^775 ≤ 21295899823449^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658074907 1250000000 21295899823449 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539419481/1000000000 : ℝ)^1031 ≤ (43992226065173/100000000000000 : ℝ)^775 := by
    have hnat : (539419481 : ℕ)^1031*100000000000000^775 ≤ 43992226065173^775*1000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539419481 1000000000 43992226065173 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209204427/10000000000 : ℝ), (658074907/1250000000 : ℝ), (539419481/1000000000 : ℝ)] ![(3353993567021/25000000000000 : ℝ), (21295899823449/50000000000000 : ℝ), (43992226065173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209204427/10000000000 : ℝ)|^1031 ≤ (3353993567021/25000000000000 : ℝ)^775
        have hw : |(-2209204427/10000000000 : ℝ)|=(2209204427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658074907/1250000000 : ℝ)|^1031 ≤ (21295899823449/50000000000000 : ℝ)^775
        have hw : |(658074907/1250000000 : ℝ)|=(658074907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539419481/1000000000 : ℝ)|^1031 ≤ (43992226065173/100000000000000 : ℝ)^775
        have hw : |(539419481/1000000000 : ℝ)|=(539419481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s9_5 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4377087211/10000000000 : ℝ)*x 0 + (4505679509/10000000000 : ℝ)*x 1 + (42522431/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377087211/10000000000 : ℝ)^1031 ≤ (33316591889579/100000000000000 : ℝ)^775 := by
    have hnat : (4377087211 : ℕ)^1031*100000000000000^775 ≤ 33316591889579^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377087211 10000000000 33316591889579 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505679509/10000000000 : ℝ)^1031 ≤ (34624977884667/100000000000000 : ℝ)^775 := by
    have hnat : (4505679509 : ℕ)^1031*100000000000000^775 ≤ 34624977884667^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505679509 10000000000 34624977884667 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42522431/100000000 : ℝ)^1031 ≤ (32058430204147/100000000000000 : ℝ)^775 := by
    have hnat : (42522431 : ℕ)^1031*100000000000000^775 ≤ 32058430204147^775*100000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42522431 100000000 32058430204147 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377087211/10000000000 : ℝ), (4505679509/10000000000 : ℝ), (42522431/100000000 : ℝ)] ![(33316591889579/100000000000000 : ℝ), (34624977884667/100000000000000 : ℝ), (32058430204147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377087211/10000000000 : ℝ)|^1031 ≤ (33316591889579/100000000000000 : ℝ)^775
        have hw : |(4377087211/10000000000 : ℝ)|=(4377087211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505679509/10000000000 : ℝ)|^1031 ≤ (34624977884667/100000000000000 : ℝ)^775
        have hw : |(4505679509/10000000000 : ℝ)|=(4505679509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42522431/100000000 : ℝ)|^1031 ≤ (32058430204147/100000000000000 : ℝ)^775
        have hw : |(42522431/100000000 : ℝ)|=(42522431/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1055_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3499/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2809/25000 : ℝ) ^ (8247/2048 : ℝ) ≤ (15029711876072893/100000000000000000000 : ℝ) := by
    have hpowers : (2809/25000 : ℝ)^8247 ≤ (15029711876072893/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2809 : ℕ)^8247*100000000000000000000^2048 ≤ 15029711876072893^2048*25000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 25000 15029711876072893 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/25000 : ℝ)) (X := (15029711876072893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3499/25000 : ℝ) ^ (8247/2048 : ℝ) ≤ (36398314279913249/100000000000000000000 : ℝ) := by
    have hpowers : (3499/25000 : ℝ)^8247 ≤ (36398314279913249/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3499 : ℕ)^8247*100000000000000000000^2048 ≤ 36398314279913249^2048*25000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3499 25000 36398314279913249 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3499/25000 : ℝ)) (X := (36398314279913249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015029711876072893/50000000000000000000 : ℝ) ≤ (1250093298693811/1250000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50015029711876072893/50000000000000000000 : ℝ)^2048 ≤ (1250093298693811/1250000000000000 : ℝ)^8247 := by
      have hnat : (50015029711876072893 : ℕ)^2048*1250000000000000^8247 ≤ 1250093298693811^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015029711876072893 50000000000000000000 1250093298693811 1250000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250093298693811/1250000000000000 : ℝ)) (X := (50015029711876072893/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025714013077993071/50000000000000000000 : ℝ) ≤ (1000127687942449/1000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50025714013077993071/50000000000000000000 : ℝ)^2048 ≤ (1000127687942449/1000000000000000 : ℝ)^8247 := by
      have hnat : (50025714013077993071 : ℕ)^2048*1000000000000000^8247 ≤ 1000127687942449^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025714013077993071 50000000000000000000 1000127687942449 1000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000127687942449/1000000000000000 : ℝ)) (X := (50025714013077993071/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036398314279913249/50000000000000000000 : ℝ) ≤ (2500451842324623/2500000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50036398314279913249/50000000000000000000 : ℝ)^2048 ≤ (2500451842324623/2500000000000000 : ℝ)^8247 := by
      have hnat : (50036398314279913249 : ℕ)^2048*2500000000000000^8247 ≤ 2500451842324623^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036398314279913249 50000000000000000000 2500451842324623 2500000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500451842324623/2500000000000000 : ℝ)) (X := (50036398314279913249/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15029711876072893/100000000000000000000 : ℝ) ≤ ((1724383679169423371/1725000000000000000 : ℝ)+2*(265244937001/138000000000000 : ℝ)*(2809/25000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (1724383679169423371/1725000000000000000 : ℝ)+2*(265244937001/138000000000000 : ℝ)*(2809/25000 : ℝ)=(1250093298693811/1250000000000000 : ℝ) by norm_num, show 1+2*(15029711876072893/100000000000000000000 : ℝ)=(50015029711876072893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36398314279913249/100000000000000000000 : ℝ)+(15029711876072893/100000000000000000000 : ℝ) ≤ ((1724383679169423371/1725000000000000000 : ℝ)+(265244937001/138000000000000 : ℝ)*((3499/25000 : ℝ)+(2809/25000 : ℝ)))^(8247/2048 : ℝ) := by
    rw [show (1724383679169423371/1725000000000000000 : ℝ)+(265244937001/138000000000000 : ℝ)*((3499/25000 : ℝ)+(2809/25000 : ℝ))=(1000127687942449/1000000000000000 : ℝ) by norm_num, show 1+(36398314279913249/100000000000000000000 : ℝ)+(15029711876072893/100000000000000000000 : ℝ)=(50025714013077993071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36398314279913249/100000000000000000000 : ℝ) ≤ ((1724383679169423371/1725000000000000000 : ℝ)+2*(265244937001/138000000000000 : ℝ)*(3499/25000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (1724383679169423371/1725000000000000000 : ℝ)+2*(265244937001/138000000000000 : ℝ)*(3499/25000 : ℝ)=(2500451842324623/2500000000000000 : ℝ) by norm_num, show 1+2*(36398314279913249/100000000000000000000 : ℝ)=(50036398314279913249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1724383679169423371/1725000000000000000 : ℝ)*(X 1 0+X 2 0)+(265244937001/138000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1724383679169423371/1725000000000000000 : ℝ)) (alpha := (265244937001/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1724383679169423371/1725000000000000000 : ℝ)*(X 0 1+X 2 1)+(265244937001/138000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1724383679169423371/1725000000000000000 : ℝ)) (alpha := (265244937001/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1724383679169423371/1725000000000000000 : ℝ)*(X 0 2+X 1 2)+(265244937001/138000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1724383679169423371/1725000000000000000 : ℝ)) (alpha := (265244937001/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276149851/1250000000 : ℝ)*X 0 0+(539452237/1000000000 : ℝ)*X 0 1+(2632136633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672498307/5000000000 : ℝ)*X 1 0+(-1137643031/5000000000 : ℝ)*X 1 1+(5264273121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068999317/2000000000 : ℝ)*X 2 0+(5264273193/10000000000 : ℝ)*X 2 1+(-568821501/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188538873/5000000000 : ℝ)*X 0 0+(850320647/2000000000 : ℝ)*X 0 1+(4506316599/10000000000 : ℝ)*X 0 2+(2188538873/5000000000 : ℝ)*X 1 0+(850320647/2000000000 : ℝ)*X 1 1+(4506316599/10000000000 : ℝ)*X 1 2+(2188538873/5000000000 : ℝ)*X 2 0+(850320647/2000000000 : ℝ)*X 2 1+(4506316599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2209204427/10000000000 : ℝ)*X 0 0+(658074907/1250000000 : ℝ)*X 0 1+(539419481/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4377087211/10000000000 : ℝ)*X 0 0+(4505679509/10000000000 : ℝ)*X 0 1+(42522431/100000000 : ℝ)*X 0 2+(4377087211/10000000000 : ℝ)*X 1 0+(4505679509/10000000000 : ℝ)*X 1 1+(42522431/100000000 : ℝ)*X 1 2+(4377087211/10000000000 : ℝ)*X 2 0+(4505679509/10000000000 : ℝ)*X 2 1+(42522431/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27232376052406710958607369/5750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11223449/4000000000000 : ℝ)*(base19) + (59455799/50000000000000 : ℝ)*(base23) + (99818581/100000000000000 : ℝ)*(lower2) + (17834291/50000000000000 : ℝ)*(lower4) + (7135349/100000000000000 : ℝ)*(lower5) + (5801795019676097/100000000000000 : ℝ)*(major0) + (5801795019676097/100000000000000 : ℝ)*(major1) + (2900897509838049/50000000000000 : ℝ)*(major2) + (239924892660119/3125000000000 : ℝ)*(sp0) + (767759794344633/10000000000000 : ℝ)*(sp1) + (7677598105120957/100000000000000 : ℝ)*(sp2) + (49074829524477/1250000000000 : ℝ)*(sp3) + (1658908747/100000000000000 : ℝ)*(sp4) + (5295492621/100000000000000 : ℝ)*(sp5) + (196299582872539/5000000000000 : ℝ)*(f.failure) + (1535519644806511/20000000000000 : ℝ)*(f.sum) + (3534023406641/2760000000000000000000000000 : ℝ)*base66 + (1517831782985587987/172500000000000000000000000000000 : ℝ)*base67 + (496301798445000571/86250000000000000000000000000000 : ℝ)*base70 + (962282849439412013/172500000000000000000000000000000 : ℝ)*base72 + (7447010101399/2760000000000000000000000000 : ℝ)*base73 + (441065222580000571/86250000000000000000000000000000 : ℝ)*base76 + (764843812464424513/172500000000000000000000000000000 : ℝ)*base78 + (2048286446529424513/172500000000000000000000000000000 : ℝ)*base80 + (19558101507703/6900000000000000000000000000 : ℝ)*base82 + (5482717/500000000000000000000 : ℝ)*base90 + (5482717/500000000000000000000 : ℝ)*base92 + (10482717/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1055_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1055_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1055_s10_0 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344996917/10000000000 : ℝ)*x 0 + (1316069751/2500000000 : ℝ)*x 1 + (-1137638949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344996917/10000000000 : ℝ)^1031 ≤ (2716203965897/6250000000000 : ℝ)^775 := by
    have hnat : (5344996917 : ℕ)^1031*6250000000000^775 ≤ 2716203965897^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344996917 10000000000 2716203965897 6250000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316069751/2500000000 : ℝ)^1031 ≤ (42588352933893/100000000000000 : ℝ)^775 := by
    have hnat : (1316069751 : ℕ)^1031*100000000000000^775 ≤ 42588352933893^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316069751 2500000000 42588352933893 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137638949/5000000000 : ℝ)^1031 ≤ (218005993607/1562500000000 : ℝ)^775 := by
    have hnat : (1137638949 : ℕ)^1031*1562500000000^775 ≤ 218005993607^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137638949 5000000000 218005993607 1562500000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344996917/10000000000 : ℝ), (1316069751/2500000000 : ℝ), (-1137638949/5000000000 : ℝ)] ![(2716203965897/6250000000000 : ℝ), (42588352933893/100000000000000 : ℝ), (218005993607/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344996917/10000000000 : ℝ)|^1031 ≤ (2716203965897/6250000000000 : ℝ)^775
        have hw : |(5344996917/10000000000 : ℝ)|=(5344996917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316069751/2500000000 : ℝ)|^1031 ≤ (42588352933893/100000000000000 : ℝ)^775
        have hw : |(1316069751/2500000000 : ℝ)|=(1316069751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1137638949/5000000000 : ℝ)|^1031 ≤ (218005993607/1562500000000 : ℝ)^775
        have hw : |(-1137638949/5000000000 : ℝ)|=(1137638949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s10_1 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-552300253/2500000000 : ℝ)*x 0 + (2632302527/5000000000 : ℝ)*x 1 + (2697095801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552300253/2500000000 : ℝ)^1031 ≤ (838496667451/6250000000000 : ℝ)^775 := by
    have hnat : (552300253 : ℕ)^1031*6250000000000^775 ≤ 838496667451^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552300253 2500000000 838496667451 6250000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632302527/5000000000 : ℝ)^1031 ≤ (21295931024263/50000000000000 : ℝ)^775 := by
    have hnat : (2632302527 : ℕ)^1031*50000000000000^775 ≤ 21295931024263^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632302527 5000000000 21295931024263 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697095801/5000000000 : ℝ)^1031 ≤ (43992191260257/100000000000000 : ℝ)^775 := by
    have hnat : (2697095801 : ℕ)^1031*100000000000000^775 ≤ 43992191260257^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697095801 5000000000 43992191260257 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552300253/2500000000 : ℝ), (2632302527/5000000000 : ℝ), (2697095801/5000000000 : ℝ)] ![(838496667451/6250000000000 : ℝ), (21295931024263/50000000000000 : ℝ), (43992191260257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552300253/2500000000 : ℝ)|^1031 ≤ (838496667451/6250000000000 : ℝ)^775
        have hw : |(-552300253/2500000000 : ℝ)|=(552300253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632302527/5000000000 : ℝ)|^1031 ≤ (21295931024263/50000000000000 : ℝ)^775
        have hw : |(2632302527/5000000000 : ℝ)|=(2632302527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697095801/5000000000 : ℝ)|^1031 ≤ (43992191260257/100000000000000 : ℝ)^775
        have hw : |(2697095801/5000000000 : ℝ)|=(2697095801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s10_2 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656110351/5000000000 : ℝ)*x 0 + (-1072682731/5000000000 : ℝ)*x 1 + (1348547901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656110351/5000000000 : ℝ)^1031 ≤ (8621018981641/20000000000000 : ℝ)^775 := by
    have hnat : (2656110351 : ℕ)^1031*20000000000000^775 ≤ 8621018981641^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656110351 5000000000 8621018981641 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072682731/5000000000 : ℝ)^1031 ≤ (6451356896337/50000000000000 : ℝ)^775 := by
    have hnat : (1072682731 : ℕ)^1031*50000000000000^775 ≤ 6451356896337^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072682731 5000000000 6451356896337 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348547901/2500000000 : ℝ)^1031 ≤ (10998047820489/25000000000000 : ℝ)^775 := by
    have hnat : (1348547901 : ℕ)^1031*25000000000000^775 ≤ 10998047820489^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348547901 2500000000 10998047820489 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656110351/5000000000 : ℝ), (-1072682731/5000000000 : ℝ), (1348547901/2500000000 : ℝ)] ![(8621018981641/20000000000000 : ℝ), (6451356896337/50000000000000 : ℝ), (10998047820489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656110351/5000000000 : ℝ)|^1031 ≤ (8621018981641/20000000000000 : ℝ)^775
        have hw : |(2656110351/5000000000 : ℝ)|=(2656110351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072682731/5000000000 : ℝ)|^1031 ≤ (6451356896337/50000000000000 : ℝ)^775
        have hw : |(-1072682731/5000000000 : ℝ)|=(1072682731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348547901/2500000000 : ℝ)|^1031 ≤ (10998047820489/25000000000000 : ℝ)^775
        have hw : |(1348547901/2500000000 : ℝ)|=(1348547901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s10_3 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (166006897/312500000 : ℝ)*x 0 + (5394191603/10000000000 : ℝ)*x 1 + (-107268273/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166006897/312500000 : ℝ)^1031 ≤ (21552547464897/50000000000000 : ℝ)^775 := by
    have hnat : (166006897 : ℕ)^1031*50000000000000^775 ≤ 21552547464897^775*312500000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166006897 312500000 21552547464897 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394191603/10000000000 : ℝ)^1031 ≤ (21996095635553/50000000000000 : ℝ)^775 := by
    have hnat : (5394191603 : ℕ)^1031*50000000000000^775 ≤ 21996095635553^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394191603 10000000000 21996095635553 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107268273/500000000 : ℝ)^1031 ≤ (403209805521/3125000000000 : ℝ)^775 := by
    have hnat : (107268273 : ℕ)^1031*3125000000000^775 ≤ 403209805521^775*500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107268273 500000000 403209805521 3125000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166006897/312500000 : ℝ), (5394191603/10000000000 : ℝ), (-107268273/500000000 : ℝ)] ![(21552547464897/50000000000000 : ℝ), (21996095635553/50000000000000 : ℝ), (403209805521/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166006897/312500000 : ℝ)|^1031 ≤ (21552547464897/50000000000000 : ℝ)^775
        have hw : |(166006897/312500000 : ℝ)|=(166006897/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394191603/10000000000 : ℝ)|^1031 ≤ (21996095635553/50000000000000 : ℝ)^775
        have hw : |(5394191603/10000000000 : ℝ)|=(5394191603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107268273/500000000 : ℝ)|^1031 ≤ (403209805521/3125000000000 : ℝ)^775
        have hw : |(-107268273/500000000 : ℝ)|=(107268273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s10_4 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (875417613/2000000000 : ℝ)*x 0 + (1126417383/2500000000 : ℝ)*x 1 + (4252252407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875417613/2000000000 : ℝ)^1031 ≤ (2082287533567/6250000000000 : ℝ)^775 := by
    have hnat : (875417613 : ℕ)^1031*6250000000000^775 ≤ 2082287533567^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875417613 2000000000 2082287533567 6250000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126417383/2500000000 : ℝ)^1031 ≤ (34624875887999/100000000000000 : ℝ)^775 := by
    have hnat : (1126417383 : ℕ)^1031*100000000000000^775 ≤ 34624875887999^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126417383 2500000000 34624875887999 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252252407/10000000000 : ℝ)^1031 ≤ (16029261774567/50000000000000 : ℝ)^775 := by
    have hnat : (4252252407 : ℕ)^1031*50000000000000^775 ≤ 16029261774567^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252252407 10000000000 16029261774567 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875417613/2000000000 : ℝ), (1126417383/2500000000 : ℝ), (4252252407/10000000000 : ℝ)] ![(2082287533567/6250000000000 : ℝ), (34624875887999/100000000000000 : ℝ), (16029261774567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875417613/2000000000 : ℝ)|^1031 ≤ (2082287533567/6250000000000 : ℝ)^775
        have hw : |(875417613/2000000000 : ℝ)|=(875417613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126417383/2500000000 : ℝ)|^1031 ≤ (34624875887999/100000000000000 : ℝ)^775
        have hw : |(1126417383/2500000000 : ℝ)|=(1126417383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252252407/10000000000 : ℝ)|^1031 ≤ (16029261774567/50000000000000 : ℝ)^775
        have hw : |(4252252407/10000000000 : ℝ)|=(4252252407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1055_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2799/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11237/100000 : ℝ) ^ (8247/2048 : ℝ) ≤ (15035099080593961/100000000000000000000 : ℝ) := by
    have hpowers : (11237/100000 : ℝ)^8247 ≤ (15035099080593961/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11237 : ℕ)^8247*100000000000000000000^2048 ≤ 15035099080593961^2048*100000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11237 100000 15035099080593961 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11237/100000 : ℝ)) (X := (15035099080593961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3499/25000 : ℝ) ^ (8247/2048 : ℝ) ≤ (36398314279913249/100000000000000000000 : ℝ) := by
    have hpowers : (3499/25000 : ℝ)^8247 ≤ (36398314279913249/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3499 : ℕ)^8247*100000000000000000000^2048 ≤ 36398314279913249^2048*25000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3499 25000 36398314279913249 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3499/25000 : ℝ)) (X := (36398314279913249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015035099080593961/50000000000000000000 : ℝ) ≤ (2500186664263469/2500000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50015035099080593961/50000000000000000000 : ℝ)^2048 ≤ (2500186664263469/2500000000000000 : ℝ)^8247 := by
      have hnat : (50015035099080593961 : ℕ)^2048*2500000000000000^8247 ≤ 2500186664263469^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015035099080593961 50000000000000000000 2500186664263469 2500000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500186664263469/2500000000000000 : ℝ)) (X := (50015035099080593961/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005143341336050721/10000000000000000000 : ℝ) ≤ (5000638506577357/5000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (10005143341336050721/10000000000000000000 : ℝ)^2048 ≤ (5000638506577357/5000000000000000 : ℝ)^8247 := by
      have hnat : (10005143341336050721 : ℕ)^2048*5000000000000000^8247 ≤ 5000638506577357^8247*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005143341336050721 10000000000000000000 5000638506577357 5000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000638506577357/5000000000000000 : ℝ)) (X := (10005143341336050721/10000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036398314279913249/50000000000000000000 : ℝ) ≤ (78139120072309/78125000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50036398314279913249/50000000000000000000 : ℝ)^2048 ≤ (78139120072309/78125000000000 : ℝ)^8247 := by
      have hnat : (50036398314279913249 : ℕ)^2048*78125000000000^8247 ≤ 78139120072309^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036398314279913249 50000000000000000000 78139120072309 78125000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78139120072309/78125000000000 : ℝ)) (X := (50036398314279913249/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15035099080593961/100000000000000000000 : ℝ) ≤ ((1723758800237588167/1724375000000000000 : ℝ)+2*(265178050419/137950000000000 : ℝ)*(11237/100000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (1723758800237588167/1724375000000000000 : ℝ)+2*(265178050419/137950000000000 : ℝ)*(11237/100000 : ℝ)=(2500186664263469/2500000000000000 : ℝ) by norm_num, show 1+2*(15035099080593961/100000000000000000000 : ℝ)=(50015035099080593961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36398314279913249/100000000000000000000 : ℝ)+(15035099080593961/100000000000000000000 : ℝ) ≤ ((1723758800237588167/1724375000000000000 : ℝ)+(265178050419/137950000000000 : ℝ)*((3499/25000 : ℝ)+(11237/100000 : ℝ)))^(8247/2048 : ℝ) := by
    rw [show (1723758800237588167/1724375000000000000 : ℝ)+(265178050419/137950000000000 : ℝ)*((3499/25000 : ℝ)+(11237/100000 : ℝ))=(5000638506577357/5000000000000000 : ℝ) by norm_num, show 1+(36398314279913249/100000000000000000000 : ℝ)+(15035099080593961/100000000000000000000 : ℝ)=(10005143341336050721/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36398314279913249/100000000000000000000 : ℝ) ≤ ((1723758800237588167/1724375000000000000 : ℝ)+2*(265178050419/137950000000000 : ℝ)*(3499/25000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (1723758800237588167/1724375000000000000 : ℝ)+2*(265178050419/137950000000000 : ℝ)*(3499/25000 : ℝ)=(78139120072309/78125000000000 : ℝ) by norm_num, show 1+2*(36398314279913249/100000000000000000000 : ℝ)=(50036398314279913249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1723758800237588167/1724375000000000000 : ℝ)*(X 1 0+X 2 0)+(265178050419/137950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1723758800237588167/1724375000000000000 : ℝ)) (alpha := (265178050419/137950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1723758800237588167/1724375000000000000 : ℝ)*(X 0 1+X 2 1)+(265178050419/137950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1723758800237588167/1724375000000000000 : ℝ)) (alpha := (265178050419/137950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1723758800237588167/1724375000000000000 : ℝ)*(X 0 2+X 1 2)+(265178050419/137950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1723758800237588167/1724375000000000000 : ℝ)) (alpha := (265178050419/137950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344996917/10000000000 : ℝ)*X 2 0+(1316069751/2500000000 : ℝ)*X 2 1+(-1137638949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s10_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-552300253/2500000000 : ℝ)*X 0 0+(2632302527/5000000000 : ℝ)*X 0 1+(2697095801/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s10_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2656110351/5000000000 : ℝ)*X 1 0+(-1072682731/5000000000 : ℝ)*X 1 1+(1348547901/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s10_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((166006897/312500000 : ℝ)*X 2 0+(5394191603/10000000000 : ℝ)*X 2 1+(-107268273/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s10_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((875417613/2000000000 : ℝ)*X 0 0+(1126417383/2500000000 : ℝ)*X 0 1+(4252252407/10000000000 : ℝ)*X 0 2+(875417613/2000000000 : ℝ)*X 1 0+(1126417383/2500000000 : ℝ)*X 1 1+(4252252407/10000000000 : ℝ)*X 1 2+(875417613/2000000000 : ℝ)*X 2 0+(1126417383/2500000000 : ℝ)*X 2 1+(4252252407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s10_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89052820540961074115325807/43109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95795543/25000000000000 : ℝ)*(base19) + (426049361/100000000000000 : ℝ)*(base23) + (67242417/50000000000000 : ℝ)*(lower1) + (43544893/100000000000000 : ℝ)*(upper3) + (4343661/25000000000000 : ℝ)*(lower4) + (10074671/25000000000000 : ℝ)*(upper5) + (2915724348813193/50000000000000 : ℝ)*(major0) + (2915724348813193/50000000000000 : ℝ)*(major1) + (2915724348813193/50000000000000 : ℝ)*(major2) + (146981399/12500000000000 : ℝ)*(sp0) + (7716839449463443/100000000000000 : ℝ)*(sp1) + (7716839066281271/100000000000000 : ℝ)*(sp2) + (771683784756289/10000000000000 : ℝ)*(sp3) + (3946057876931259/100000000000000 : ℝ)*(sp4) + (3946057876931259/100000000000000 : ℝ)*(f.failure) + (7716839449463443/100000000000000 : ℝ)*(f.sum) + (4569755253137/13795000000000000000000000000 : ℝ)*base66 + (2870074113064562231/86218750000000000000000000000000 : ℝ)*base67 + (245126098162031519/86218750000000000000000000000000 : ℝ)*base70 + (8748187900609780981/86218750000000000000000000000000 : ℝ)*base71 + (4299768891201/6897500000000000000000000000 : ℝ)*base74 + (6616178117895844019/86218750000000000000000000000000 : ℝ)*base76 + (270317406955468481/86218750000000000000000000000000 : ℝ)*base77 + (497304409325687231/86218750000000000000000000000000 : ℝ)*base79 + (43488754255853/13795000000000000000000000000 : ℝ)*base81 + (13906877/10000000000000000000000 : ℝ)*base90 + (13906877/10000000000000000000000 : ℝ)*base92 + (13906877/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1055_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1055_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1055_box_0 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-207936531/1000000000 : ℝ)*x 0 + (672189033/1250000000 : ℝ)*x 1 + (537751199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207936531/1000000000 : ℝ)^1031 ≤ (6188678738213/50000000000000 : ℝ)^775 := by
    have hnat : (207936531 : ℕ)^1031*50000000000000^775 ≤ 6188678738213^775*1000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207936531 1000000000 6188678738213 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672189033/1250000000 : ℝ)^1031 ≤ (21905661367599/50000000000000 : ℝ)^775 := by
    have hnat : (672189033 : ℕ)^1031*50000000000000^775 ≤ 21905661367599^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672189033 1250000000 21905661367599 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537751199/1000000000 : ℝ)^1031 ≤ (43811319765499/100000000000000 : ℝ)^775 := by
    have hnat : (537751199 : ℕ)^1031*100000000000000^775 ≤ 43811319765499^775*1000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537751199 1000000000 43811319765499 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207936531/1000000000 : ℝ), (672189033/1250000000 : ℝ), (537751199/1000000000 : ℝ)] ![(6188678738213/50000000000000 : ℝ), (21905661367599/50000000000000 : ℝ), (43811319765499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207936531/1000000000 : ℝ)|^1031 ≤ (6188678738213/50000000000000 : ℝ)^775
        have hw : |(-207936531/1000000000 : ℝ)|=(207936531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672189033/1250000000 : ℝ)|^1031 ≤ (21905661367599/50000000000000 : ℝ)^775
        have hw : |(672189033/1250000000 : ℝ)|=(672189033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537751199/1000000000 : ℝ)|^1031 ≤ (43811319765499/100000000000000 : ℝ)^775
        have hw : |(537751199/1000000000 : ℝ)|=(537751199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_1 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5295079553/10000000000 : ℝ)*x 0 + (-2190926877/10000000000 : ℝ)*x 1 + (1344378061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295079553/10000000000 : ℝ)^1031 ≤ (10730040126243/25000000000000 : ℝ)^775 := by
    have hnat : (5295079553 : ℕ)^1031*25000000000000^775 ≤ 10730040126243^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295079553 10000000000 10730040126243 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190926877/10000000000 : ℝ)^1031 ≤ (6634258478353/50000000000000 : ℝ)^775 := by
    have hnat : (2190926877 : ℕ)^1031*50000000000000^775 ≤ 6634258478353^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190926877 10000000000 6634258478353 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344378061/2500000000 : ℝ)^1031 ≤ (1369103828701/3125000000000 : ℝ)^775 := by
    have hnat : (1344378061 : ℕ)^1031*3125000000000^775 ≤ 1369103828701^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344378061 2500000000 1369103828701 3125000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295079553/10000000000 : ℝ), (-2190926877/10000000000 : ℝ), (1344378061/2500000000 : ℝ)] ![(10730040126243/25000000000000 : ℝ), (6634258478353/50000000000000 : ℝ), (1369103828701/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295079553/10000000000 : ℝ)|^1031 ≤ (10730040126243/25000000000000 : ℝ)^775
        have hw : |(5295079553/10000000000 : ℝ)|=(5295079553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190926877/10000000000 : ℝ)|^1031 ≤ (6634258478353/50000000000000 : ℝ)^775
        have hw : |(-2190926877/10000000000 : ℝ)|=(2190926877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344378061/2500000000 : ℝ)|^1031 ≤ (1369103828701/3125000000000 : ℝ)^775
        have hw : |(1344378061/2500000000 : ℝ)|=(1344378061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_2 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5295079571/10000000000 : ℝ)*x 0 + (5377512087/10000000000 : ℝ)*x 1 + (-273865883/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295079571/10000000000 : ℝ)^1031 ≤ (42920160699069/100000000000000 : ℝ)^775 := by
    have hnat : (5295079571 : ℕ)^1031*100000000000000^775 ≤ 42920160699069^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295079571 10000000000 42920160699069 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377512087/10000000000 : ℝ)^1031 ≤ (8762264163363/20000000000000 : ℝ)^775 := by
    have hnat : (5377512087 : ℕ)^1031*20000000000000^775 ≤ 8762264163363^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377512087 10000000000 8762264163363 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273865883/1250000000 : ℝ)^1031 ≤ (13268518463289/100000000000000 : ℝ)^775 := by
    have hnat : (273865883 : ℕ)^1031*100000000000000^775 ≤ 13268518463289^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273865883 1250000000 13268518463289 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295079571/10000000000 : ℝ), (5377512087/10000000000 : ℝ), (-273865883/1250000000 : ℝ)] ![(42920160699069/100000000000000 : ℝ), (8762264163363/20000000000000 : ℝ), (13268518463289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295079571/10000000000 : ℝ)|^1031 ≤ (42920160699069/100000000000000 : ℝ)^775
        have hw : |(5295079571/10000000000 : ℝ)|=(5295079571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377512087/10000000000 : ℝ)|^1031 ≤ (8762264163363/20000000000000 : ℝ)^775
        have hw : |(5377512087/10000000000 : ℝ)|=(5377512087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273865883/1250000000 : ℝ)|^1031 ≤ (13268518463289/100000000000000 : ℝ)^775
        have hw : |(-273865883/1250000000 : ℝ)|=(273865883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_3 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2242791869/5000000000 : ℝ)*x 0 + (4324995431/10000000000 : ℝ)*x 1 + (67578053/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242791869/5000000000 : ℝ)^1031 ≤ (17209843305379/50000000000000 : ℝ)^775 := by
    have hnat : (2242791869 : ℕ)^1031*50000000000000^775 ≤ 17209843305379^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242791869 5000000000 17209843305379 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4324995431/10000000000 : ℝ)^1031 ≤ (16395078440641/50000000000000 : ℝ)^775 := by
    have hnat : (4324995431 : ℕ)^1031*50000000000000^775 ≤ 16395078440641^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324995431 10000000000 16395078440641 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67578053/156250000 : ℝ)^1031 ≤ (32790156487931/100000000000000 : ℝ)^775 := by
    have hnat : (67578053 : ℕ)^1031*100000000000000^775 ≤ 32790156487931^775*156250000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67578053 156250000 32790156487931 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242791869/5000000000 : ℝ), (4324995431/10000000000 : ℝ), (67578053/156250000 : ℝ)] ![(17209843305379/50000000000000 : ℝ), (16395078440641/50000000000000 : ℝ), (32790156487931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242791869/5000000000 : ℝ)|^1031 ≤ (17209843305379/50000000000000 : ℝ)^775
        have hw : |(2242791869/5000000000 : ℝ)|=(2242791869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4324995431/10000000000 : ℝ)|^1031 ≤ (16395078440641/50000000000000 : ℝ)^775
        have hw : |(4324995431/10000000000 : ℝ)|=(4324995431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67578053/156250000 : ℝ)|^1031 ≤ (32790156487931/100000000000000 : ℝ)^775
        have hw : |(67578053/156250000 : ℝ)|=(67578053/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_4 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-58510497/250000000 : ℝ)*x 0 + (1055985549/2000000000 : ℝ)*x 1 + (211197109/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58510497/250000000 : ℝ)^1031 ≤ (2897258644723/20000000000000 : ℝ)^775 := by
    have hnat : (58510497 : ℕ)^1031*20000000000000^775 ≤ 2897258644723^775*250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58510497 250000000 2897258644723 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055985549/2000000000 : ℝ)^1031 ≤ (42756853490673/100000000000000 : ℝ)^775 := by
    have hnat : (1055985549 : ℕ)^1031*100000000000000^775 ≤ 42756853490673^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055985549 2000000000 42756853490673 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211197109/400000000 : ℝ)^1031 ≤ (21378426637607/50000000000000 : ℝ)^775 := by
    have hnat : (211197109 : ℕ)^1031*50000000000000^775 ≤ 21378426637607^775*400000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211197109 400000000 21378426637607 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58510497/250000000 : ℝ), (1055985549/2000000000 : ℝ), (211197109/400000000 : ℝ)] ![(2897258644723/20000000000000 : ℝ), (42756853490673/100000000000000 : ℝ), (21378426637607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58510497/250000000 : ℝ)|^1031 ≤ (2897258644723/20000000000000 : ℝ)^775
        have hw : |(-58510497/250000000 : ℝ)|=(58510497/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055985549/2000000000 : ℝ)|^1031 ≤ (42756853490673/100000000000000 : ℝ)^775
        have hw : |(1055985549/2000000000 : ℝ)|=(1055985549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211197109/400000000 : ℝ)|^1031 ≤ (21378426637607/50000000000000 : ℝ)^775
        have hw : |(211197109/400000000 : ℝ)|=(211197109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_5 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5364159359/10000000000 : ℝ)*x 0 + (-1114521847/5000000000 : ℝ)*x 1 + (5279927721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364159359/10000000000 : ℝ)^1031 ≤ (43666659080367/100000000000000 : ℝ)^775 := by
    have hnat : (5364159359 : ℕ)^1031*100000000000000^775 ≤ 43666659080367^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364159359 10000000000 43666659080367 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114521847/5000000000 : ℝ)^1031 ≤ (6788243831083/50000000000000 : ℝ)^775 := by
    have hnat : (1114521847 : ℕ)^1031*50000000000000^775 ≤ 6788243831083^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114521847 5000000000 6788243831083 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279927721/10000000000 : ℝ)^1031 ≤ (21378426616061/50000000000000 : ℝ)^775 := by
    have hnat : (5279927721 : ℕ)^1031*50000000000000^775 ≤ 21378426616061^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279927721 10000000000 21378426616061 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364159359/10000000000 : ℝ), (-1114521847/5000000000 : ℝ), (5279927721/10000000000 : ℝ)] ![(43666659080367/100000000000000 : ℝ), (6788243831083/50000000000000 : ℝ), (21378426616061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364159359/10000000000 : ℝ)|^1031 ≤ (43666659080367/100000000000000 : ℝ)^775
        have hw : |(5364159359/10000000000 : ℝ)|=(5364159359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114521847/5000000000 : ℝ)|^1031 ≤ (6788243831083/50000000000000 : ℝ)^775
        have hw : |(-1114521847/5000000000 : ℝ)|=(1114521847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279927721/10000000000 : ℝ)|^1031 ≤ (21378426616061/50000000000000 : ℝ)^775
        have hw : |(5279927721/10000000000 : ℝ)|=(5279927721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_6 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2682079657/5000000000 : ℝ)*x 0 + (5279927771/10000000000 : ℝ)*x 1 + (-2229043689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682079657/5000000000 : ℝ)^1031 ≤ (43666658593043/100000000000000 : ℝ)^775 := by
    have hnat : (2682079657 : ℕ)^1031*100000000000000^775 ≤ 43666658593043^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682079657 5000000000 43666658593043 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279927771/10000000000 : ℝ)^1031 ≤ (42756853770769/100000000000000 : ℝ)^775 := by
    have hnat : (5279927771 : ℕ)^1031*100000000000000^775 ≤ 42756853770769^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279927771 10000000000 42756853770769 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229043689/10000000000 : ℝ)^1031 ≤ (13576487621653/100000000000000 : ℝ)^775 := by
    have hnat : (2229043689 : ℕ)^1031*100000000000000^775 ≤ 13576487621653^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229043689 10000000000 13576487621653 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682079657/5000000000 : ℝ), (5279927771/10000000000 : ℝ), (-2229043689/10000000000 : ℝ)] ![(43666658593043/100000000000000 : ℝ), (42756853770769/100000000000000 : ℝ), (13576487621653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682079657/5000000000 : ℝ)|^1031 ≤ (43666658593043/100000000000000 : ℝ)^775
        have hw : |(2682079657/5000000000 : ℝ)|=(2682079657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279927771/10000000000 : ℝ)|^1031 ≤ (42756853770769/100000000000000 : ℝ)^775
        have hw : |(5279927771/10000000000 : ℝ)|=(5279927771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229043689/10000000000 : ℝ)|^1031 ≤ (13576487621653/100000000000000 : ℝ)^775
        have hw : |(-2229043689/10000000000 : ℝ)|=(2229043689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_7 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4268248377/10000000000 : ℝ)*x 0 + (554205197/1250000000 : ℝ)*x 1 + (4433641511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268248377/10000000000 : ℝ)^1031 ≤ (32219055521449/100000000000000 : ℝ)^775 := by
    have hnat : (4268248377 : ℕ)^1031*100000000000000^775 ≤ 32219055521449^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268248377 10000000000 32219055521449 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554205197/1250000000 : ℝ)^1031 ≤ (33890472557687/100000000000000 : ℝ)^775 := by
    have hnat : (554205197 : ℕ)^1031*100000000000000^775 ≤ 33890472557687^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554205197 1250000000 33890472557687 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4433641511/10000000000 : ℝ)^1031 ≤ (8472617974177/25000000000000 : ℝ)^775 := by
    have hnat : (4433641511 : ℕ)^1031*25000000000000^775 ≤ 8472617974177^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433641511 10000000000 8472617974177 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268248377/10000000000 : ℝ), (554205197/1250000000 : ℝ), (4433641511/10000000000 : ℝ)] ![(32219055521449/100000000000000 : ℝ), (33890472557687/100000000000000 : ℝ), (8472617974177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268248377/10000000000 : ℝ)|^1031 ≤ (32219055521449/100000000000000 : ℝ)^775
        have hw : |(4268248377/10000000000 : ℝ)|=(4268248377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554205197/1250000000 : ℝ)|^1031 ≤ (33890472557687/100000000000000 : ℝ)^775
        have hw : |(554205197/1250000000 : ℝ)|=(554205197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4433641511/10000000000 : ℝ)|^1031 ≤ (8472617974177/25000000000000 : ℝ)^775
        have hw : |(4433641511/10000000000 : ℝ)|=(4433641511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_8 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-142871027/625000000 : ℝ)*x 0 + (2606866307/5000000000 : ℝ)*x 1 + (10774221/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142871027/625000000 : ℝ)^1031 ≤ (14039400555413/100000000000000 : ℝ)^775 := by
    have hnat : (142871027 : ℕ)^1031*100000000000000^775 ≤ 14039400555413^775*625000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142871027 625000000 14039400555413 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606866307/5000000000 : ℝ)^1031 ≤ (21022608648247/50000000000000 : ℝ)^775 := by
    have hnat : (2606866307 : ℕ)^1031*50000000000000^775 ≤ 21022608648247^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606866307 5000000000 21022608648247 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10774221/20000000 : ℝ)^1031 ≤ (1097884553277/2500000000000 : ℝ)^775 := by
    have hnat : (10774221 : ℕ)^1031*2500000000000^775 ≤ 1097884553277^775*20000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10774221 20000000 1097884553277 2500000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-142871027/625000000 : ℝ), (2606866307/5000000000 : ℝ), (10774221/20000000 : ℝ)] ![(14039400555413/100000000000000 : ℝ), (21022608648247/50000000000000 : ℝ), (1097884553277/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-142871027/625000000 : ℝ)|^1031 ≤ (14039400555413/100000000000000 : ℝ)^775
        have hw : |(-142871027/625000000 : ℝ)|=(142871027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606866307/5000000000 : ℝ)|^1031 ≤ (21022608648247/50000000000000 : ℝ)^775
        have hw : |(2606866307/5000000000 : ℝ)|=(2606866307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10774221/20000000 : ℝ)|^1031 ≤ (1097884553277/2500000000000 : ℝ)^775
        have hw : |(10774221/20000000 : ℝ)|=(10774221/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_9 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322070473/2500000000 : ℝ)*x 0 + (-68347059/312500000 : ℝ)*x 1 + (5387110533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322070473/2500000000 : ℝ)^1031 ≤ (21423437912629/50000000000000 : ℝ)^775 := by
    have hnat : (1322070473 : ℕ)^1031*50000000000000^775 ≤ 21423437912629^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322070473 2500000000 21423437912629 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68347059/312500000 : ℝ)^1031 ≤ (6618870835657/50000000000000 : ℝ)^775 := by
    have hnat : (68347059 : ℕ)^1031*50000000000000^775 ≤ 6618870835657^775*312500000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68347059 312500000 6618870835657 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387110533/10000000000 : ℝ)^1031 ≤ (10978845622239/25000000000000 : ℝ)^775 := by
    have hnat : (5387110533 : ℕ)^1031*25000000000000^775 ≤ 10978845622239^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387110533 10000000000 10978845622239 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322070473/2500000000 : ℝ), (-68347059/312500000 : ℝ), (5387110533/10000000000 : ℝ)] ![(21423437912629/50000000000000 : ℝ), (6618870835657/50000000000000 : ℝ), (10978845622239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322070473/2500000000 : ℝ)|^1031 ≤ (21423437912629/50000000000000 : ℝ)^775
        have hw : |(1322070473/2500000000 : ℝ)|=(1322070473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68347059/312500000 : ℝ)|^1031 ≤ (6618870835657/50000000000000 : ℝ)^775
        have hw : |(-68347059/312500000 : ℝ)|=(68347059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387110533/10000000000 : ℝ)|^1031 ≤ (10978845622239/25000000000000 : ℝ)^775
        have hw : |(5387110533/10000000000 : ℝ)|=(5387110533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_10 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322070443/2500000000 : ℝ)*x 0 + (5387109689/10000000000 : ℝ)*x 1 + (-437421437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322070443/2500000000 : ℝ)^1031 ≤ (10711718632957/25000000000000 : ℝ)^775 := by
    have hnat : (1322070443 : ℕ)^1031*25000000000000^775 ≤ 10711718632957^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322070443 2500000000 10711718632957 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387109689/10000000000 : ℝ)^1031 ≤ (1756614933441/4000000000000 : ℝ)^775 := by
    have hnat : (5387109689 : ℕ)^1031*4000000000000^775 ≤ 1756614933441^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387109689 10000000000 1756614933441 4000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437421437/2000000000 : ℝ)^1031 ≤ (6618876057347/50000000000000 : ℝ)^775 := by
    have hnat : (437421437 : ℕ)^1031*50000000000000^775 ≤ 6618876057347^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437421437 2000000000 6618876057347 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322070443/2500000000 : ℝ), (5387109689/10000000000 : ℝ), (-437421437/2000000000 : ℝ)] ![(10711718632957/25000000000000 : ℝ), (1756614933441/4000000000000 : ℝ), (6618876057347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322070443/2500000000 : ℝ)|^1031 ≤ (10711718632957/25000000000000 : ℝ)^775
        have hw : |(1322070443/2500000000 : ℝ)|=(1322070443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387109689/10000000000 : ℝ)|^1031 ≤ (1756614933441/4000000000000 : ℝ)^775
        have hw : |(5387109689/10000000000 : ℝ)|=(5387109689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437421437/2000000000 : ℝ)|^1031 ≤ (6618876057347/50000000000000 : ℝ)^775
        have hw : |(-437421437/2000000000 : ℝ)|=(437421437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_11 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (281667989/625000000 : ℝ)*x 0 + (862860493/2000000000 : ℝ)*x 1 + (4314303267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281667989/625000000 : ℝ)^1031 ≤ (34635286455261/100000000000000 : ℝ)^775 := by
    have hnat : (281667989 : ℕ)^1031*100000000000000^775 ≤ 34635286455261^775*625000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281667989 625000000 34635286455261 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862860493/2000000000 : ℝ)^1031 ≤ (16341176361053/50000000000000 : ℝ)^775 := by
    have hnat : (862860493 : ℕ)^1031*50000000000000^775 ≤ 16341176361053^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862860493 2000000000 16341176361053 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314303267/10000000000 : ℝ)^1031 ≤ (32682360804389/100000000000000 : ℝ)^775 := by
    have hnat : (4314303267 : ℕ)^1031*100000000000000^775 ≤ 32682360804389^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314303267 10000000000 32682360804389 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(281667989/625000000 : ℝ), (862860493/2000000000 : ℝ), (4314303267/10000000000 : ℝ)] ![(34635286455261/100000000000000 : ℝ), (16341176361053/50000000000000 : ℝ), (32682360804389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(281667989/625000000 : ℝ)|^1031 ≤ (34635286455261/100000000000000 : ℝ)^775
        have hw : |(281667989/625000000 : ℝ)|=(281667989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862860493/2000000000 : ℝ)|^1031 ≤ (16341176361053/50000000000000 : ℝ)^775
        have hw : |(862860493/2000000000 : ℝ)|=(862860493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4314303267/10000000000 : ℝ)|^1031 ≤ (32682360804389/100000000000000 : ℝ)^775
        have hw : |(4314303267/10000000000 : ℝ)|=(4314303267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_12 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134225091/10000000000 : ℝ)*x 0 + (5442363349/10000000000 : ℝ)*x 1 + (263596643/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134225091/10000000000 : ℝ)^1031 ≤ (2562731552431/20000000000000 : ℝ)^775 := by
    have hnat : (2134225091 : ℕ)^1031*20000000000000^775 ≤ 2562731552431^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134225091 10000000000 2562731552431 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442363349/10000000000 : ℝ)^1031 ≤ (44515595699469/100000000000000 : ℝ)^775 := by
    have hnat : (5442363349 : ℕ)^1031*100000000000000^775 ≤ 44515595699469^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442363349 10000000000 44515595699469 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263596643/500000000 : ℝ)^1031 ≤ (42670746526031/100000000000000 : ℝ)^775 := by
    have hnat : (263596643 : ℕ)^1031*100000000000000^775 ≤ 42670746526031^775*500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263596643 500000000 42670746526031 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134225091/10000000000 : ℝ), (5442363349/10000000000 : ℝ), (263596643/500000000 : ℝ)] ![(2562731552431/20000000000000 : ℝ), (44515595699469/100000000000000 : ℝ), (42670746526031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134225091/10000000000 : ℝ)|^1031 ≤ (2562731552431/20000000000000 : ℝ)^775
        have hw : |(-2134225091/10000000000 : ℝ)|=(2134225091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442363349/10000000000 : ℝ)|^1031 ≤ (44515595699469/100000000000000 : ℝ)^775
        have hw : |(5442363349/10000000000 : ℝ)|=(5442363349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263596643/500000000 : ℝ)|^1031 ≤ (42670746526031/100000000000000 : ℝ)^775
        have hw : |(263596643/500000000 : ℝ)|=(263596643/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_13 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1073963233/2000000000 : ℝ)*x 0 + (-139506729/625000000 : ℝ)*x 1 + (5271933257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073963233/2000000000 : ℝ)^1031 ≤ (10931982421007/25000000000000 : ℝ)^775 := by
    have hnat : (1073963233 : ℕ)^1031*25000000000000^775 ≤ 10931982421007^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073963233 2000000000 10931982421007 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139506729/625000000 : ℝ)^1031 ≤ (6800659750289/50000000000000 : ℝ)^775 := by
    have hnat : (139506729 : ℕ)^1031*50000000000000^775 ≤ 6800659750289^775*625000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139506729 625000000 6800659750289 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271933257/10000000000 : ℝ)^1031 ≤ (42670750800753/100000000000000 : ℝ)^775 := by
    have hnat : (5271933257 : ℕ)^1031*100000000000000^775 ≤ 42670750800753^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271933257 10000000000 42670750800753 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073963233/2000000000 : ℝ), (-139506729/625000000 : ℝ), (5271933257/10000000000 : ℝ)] ![(10931982421007/25000000000000 : ℝ), (6800659750289/50000000000000 : ℝ), (42670750800753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073963233/2000000000 : ℝ)|^1031 ≤ (10931982421007/25000000000000 : ℝ)^775
        have hw : |(1073963233/2000000000 : ℝ)|=(1073963233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139506729/625000000 : ℝ)|^1031 ≤ (6800659750289/50000000000000 : ℝ)^775
        have hw : |(-139506729/625000000 : ℝ)|=(139506729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271933257/10000000000 : ℝ)|^1031 ≤ (42670750800753/100000000000000 : ℝ)^775
        have hw : |(5271933257/10000000000 : ℝ)|=(5271933257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_14 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369816477/10000000000 : ℝ)*x 0 + (527193319/1000000000 : ℝ)*x 1 + (-279013417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369816477/10000000000 : ℝ)^1031 ≤ (2732995816499/6250000000000 : ℝ)^775 := by
    have hnat : (5369816477 : ℕ)^1031*6250000000000^775 ≤ 2732995816499^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369816477 10000000000 2732995816499 6250000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527193319/1000000000 : ℝ)^1031 ≤ (21335375039663/50000000000000 : ℝ)^775 := by
    have hnat : (527193319 : ℕ)^1031*50000000000000^775 ≤ 21335375039663^775*1000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527193319 1000000000 21335375039663 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279013417/1250000000 : ℝ)^1031 ≤ (1360131684171/10000000000000 : ℝ)^775 := by
    have hnat : (279013417 : ℕ)^1031*10000000000000^775 ≤ 1360131684171^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279013417 1250000000 1360131684171 10000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369816477/10000000000 : ℝ), (527193319/1000000000 : ℝ), (-279013417/1250000000 : ℝ)] ![(2732995816499/6250000000000 : ℝ), (21335375039663/50000000000000 : ℝ), (1360131684171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369816477/10000000000 : ℝ)|^1031 ≤ (2732995816499/6250000000000 : ℝ)^775
        have hw : |(5369816477/10000000000 : ℝ)|=(5369816477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527193319/1000000000 : ℝ)|^1031 ≤ (21335375039663/50000000000000 : ℝ)^775
        have hw : |(527193319/1000000000 : ℝ)|=(527193319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279013417/1250000000 : ℝ)|^1031 ≤ (1360131684171/10000000000000 : ℝ)^775
        have hw : |(-279013417/1250000000 : ℝ)|=(279013417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_box_15 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4250213359/10000000000 : ℝ)*x 0 + (4442536641/10000000000 : ℝ)*x 1 + (4442538061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250213359/10000000000 : ℝ)^1031 ≤ (32038074435273/100000000000000 : ℝ)^775 := by
    have hnat : (4250213359 : ℕ)^1031*100000000000000^775 ≤ 32038074435273^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250213359 10000000000 32038074435273 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4442536641/10000000000 : ℝ)^1031 ≤ (8495238887311/25000000000000 : ℝ)^775 := by
    have hnat : (4442536641 : ℕ)^1031*25000000000000^775 ≤ 8495238887311^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442536641 10000000000 8495238887311 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4442538061/10000000000 : ℝ)^1031 ≤ (33980969998647/100000000000000 : ℝ)^775 := by
    have hnat : (4442538061 : ℕ)^1031*100000000000000^775 ≤ 33980969998647^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442538061 10000000000 33980969998647 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250213359/10000000000 : ℝ), (4442536641/10000000000 : ℝ), (4442538061/10000000000 : ℝ)] ![(32038074435273/100000000000000 : ℝ), (8495238887311/25000000000000 : ℝ), (33980969998647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250213359/10000000000 : ℝ)|^1031 ≤ (32038074435273/100000000000000 : ℝ)^775
        have hw : |(4250213359/10000000000 : ℝ)|=(4250213359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4442536641/10000000000 : ℝ)|^1031 ≤ (8495238887311/25000000000000 : ℝ)^775
        have hw : |(4442536641/10000000000 : ℝ)|=(4442536641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4442538061/10000000000 : ℝ)|^1031 ≤ (33980969998647/100000000000000 : ℝ)^775
        have hw : |(4442538061/10000000000 : ℝ)|=(4442538061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1055_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59233/100000 : ℝ) ∧ (39769/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82927/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11237/100000 : ℝ) ^ (8247/2048 : ℝ) ≤ (15035099080593961/100000000000000000000 : ℝ) := by
    have hpowers : (11237/100000 : ℝ)^8247 ≤ (15035099080593961/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11237 : ℕ)^8247*100000000000000000000^2048 ≤ 15035099080593961^2048*100000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11237 100000 15035099080593961 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11237/100000 : ℝ)) (X := (15035099080593961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2799/20000 : ℝ) ^ (8247/2048 : ℝ) ≤ (9096960770204099/25000000000000000000 : ℝ) := by
    have hpowers : (2799/20000 : ℝ)^8247 ≤ (9096960770204099/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2799 : ℕ)^8247*25000000000000000000^2048 ≤ 9096960770204099^2048*20000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 20000 9096960770204099 25000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/20000 : ℝ)) (X := (9096960770204099/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015035099080593961/50000000000000000000 : ℝ) ≤ (2500186664263469/2500000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50015035099080593961/50000000000000000000 : ℝ)^2048 ≤ (2500186664263469/2500000000000000 : ℝ)^8247 := by
      have hnat : (50015035099080593961 : ℕ)^2048*2500000000000000^8247 ≤ 2500186664263469^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015035099080593961 50000000000000000000 2500186664263469 2500000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500186664263469/2500000000000000 : ℝ)) (X := (50015035099080593961/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051422942161410357/100000000000000000000 : ℝ) ≤ (10001276753221047/10000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (100051422942161410357/100000000000000000000 : ℝ)^2048 ≤ (10001276753221047/10000000000000000 : ℝ)^8247 := by
      have hnat : (100051422942161410357 : ℕ)^2048*10000000000000000^8247 ≤ 10001276753221047^8247*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051422942161410357 100000000000000000000 10001276753221047 10000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001276753221047/10000000000000000 : ℝ)) (X := (100051422942161410357/100000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509096960770204099/12500000000000000000 : ℝ) ≤ (5000903424694109/5000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (12509096960770204099/12500000000000000000 : ℝ)^2048 ≤ (5000903424694109/5000000000000000 : ℝ)^8247 := by
      have hnat : (12509096960770204099 : ℕ)^2048*5000000000000000^8247 ≤ 5000903424694109^8247*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509096960770204099 12500000000000000000 5000903424694109 5000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000903424694109/5000000000000000 : ℝ)) (X := (12509096960770204099/12500000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15035099080593961/100000000000000000000 : ℝ) ≤ ((13785072949446794477/13790000000000000000 : ℝ)+2*(530096167171/275800000000000 : ℝ)*(11237/100000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (13785072949446794477/13790000000000000000 : ℝ)+2*(530096167171/275800000000000 : ℝ)*(11237/100000 : ℝ)=(2500186664263469/2500000000000000 : ℝ) by norm_num, show 1+2*(15035099080593961/100000000000000000000 : ℝ)=(50015035099080593961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9096960770204099/25000000000000000000 : ℝ)+(15035099080593961/100000000000000000000 : ℝ) ≤ ((13785072949446794477/13790000000000000000 : ℝ)+(530096167171/275800000000000 : ℝ)*((2799/20000 : ℝ)+(11237/100000 : ℝ)))^(8247/2048 : ℝ) := by
    rw [show (13785072949446794477/13790000000000000000 : ℝ)+(530096167171/275800000000000 : ℝ)*((2799/20000 : ℝ)+(11237/100000 : ℝ))=(10001276753221047/10000000000000000 : ℝ) by norm_num, show 1+(9096960770204099/25000000000000000000 : ℝ)+(15035099080593961/100000000000000000000 : ℝ)=(100051422942161410357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9096960770204099/25000000000000000000 : ℝ) ≤ ((13785072949446794477/13790000000000000000 : ℝ)+2*(530096167171/275800000000000 : ℝ)*(2799/20000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (13785072949446794477/13790000000000000000 : ℝ)+2*(530096167171/275800000000000 : ℝ)*(2799/20000 : ℝ)=(5000903424694109/5000000000000000 : ℝ) by norm_num, show 1+2*(9096960770204099/25000000000000000000 : ℝ)=(12509096960770204099/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13785072949446794477/13790000000000000000 : ℝ)*(X 1 0+X 2 0)+(530096167171/275800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (13785072949446794477/13790000000000000000 : ℝ)) (alpha := (530096167171/275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13785072949446794477/13790000000000000000 : ℝ)*(X 0 1+X 2 1)+(530096167171/275800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (13785072949446794477/13790000000000000000 : ℝ)) (alpha := (530096167171/275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13785072949446794477/13790000000000000000 : ℝ)*(X 0 2+X 1 2)+(530096167171/275800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (13785072949446794477/13790000000000000000 : ℝ)) (alpha := (530096167171/275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207936531/1000000000 : ℝ)*X 0 0+(672189033/1250000000 : ℝ)*X 0 1+(537751199/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295079553/10000000000 : ℝ)*X 1 0+(-2190926877/10000000000 : ℝ)*X 1 1+(1344378061/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295079571/10000000000 : ℝ)*X 2 0+(5377512087/10000000000 : ℝ)*X 2 1+(-273865883/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2242791869/5000000000 : ℝ)*X 0 0+(4324995431/10000000000 : ℝ)*X 0 1+(67578053/156250000 : ℝ)*X 0 2+(2242791869/5000000000 : ℝ)*X 1 0+(4324995431/10000000000 : ℝ)*X 1 1+(67578053/156250000 : ℝ)*X 1 2+(2242791869/5000000000 : ℝ)*X 2 0+(4324995431/10000000000 : ℝ)*X 2 1+(67578053/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-58510497/250000000 : ℝ)*X 0 0+(1055985549/2000000000 : ℝ)*X 0 1+(211197109/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364159359/10000000000 : ℝ)*X 1 0+(-1114521847/5000000000 : ℝ)*X 1 1+(5279927721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682079657/5000000000 : ℝ)*X 2 0+(5279927771/10000000000 : ℝ)*X 2 1+(-2229043689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268248377/10000000000 : ℝ)*X 0 0+(554205197/1250000000 : ℝ)*X 0 1+(4433641511/10000000000 : ℝ)*X 0 2+(4268248377/10000000000 : ℝ)*X 1 0+(554205197/1250000000 : ℝ)*X 1 1+(4433641511/10000000000 : ℝ)*X 1 2+(4268248377/10000000000 : ℝ)*X 2 0+(554205197/1250000000 : ℝ)*X 2 1+(4433641511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-142871027/625000000 : ℝ)*X 0 0+(2606866307/5000000000 : ℝ)*X 0 1+(10774221/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322070473/2500000000 : ℝ)*X 1 0+(-68347059/312500000 : ℝ)*X 1 1+(5387110533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322070443/2500000000 : ℝ)*X 2 0+(5387109689/10000000000 : ℝ)*X 2 1+(-437421437/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((281667989/625000000 : ℝ)*X 0 0+(862860493/2000000000 : ℝ)*X 0 1+(4314303267/10000000000 : ℝ)*X 0 2+(281667989/625000000 : ℝ)*X 1 0+(862860493/2000000000 : ℝ)*X 1 1+(4314303267/10000000000 : ℝ)*X 1 2+(281667989/625000000 : ℝ)*X 2 0+(862860493/2000000000 : ℝ)*X 2 1+(4314303267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2134225091/10000000000 : ℝ)*X 0 0+(5442363349/10000000000 : ℝ)*X 0 1+(263596643/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073963233/2000000000 : ℝ)*X 1 0+(-139506729/625000000 : ℝ)*X 1 1+(5271933257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369816477/10000000000 : ℝ)*X 2 0+(527193319/1000000000 : ℝ)*X 2 1+(-279013417/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4250213359/10000000000 : ℝ)*X 0 0+(4442536641/10000000000 : ℝ)*X 0 1+(4442538061/10000000000 : ℝ)*X 0 2+(4250213359/10000000000 : ℝ)*X 1 0+(4442536641/10000000000 : ℝ)*X 1 1+(4442538061/10000000000 : ℝ)*X 1 2+(4250213359/10000000000 : ℝ)*X 2 0+(4442536641/10000000000 : ℝ)*X 2 1+(4442538061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-7661008316506142300433068427861/12312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30963927/100000000000000 : ℝ)*(upper0) + (19097993/50000000000000 : ℝ)*(upper1) + (1036757/3125000000000 : ℝ)*(upper3) + (2716519/20000000000000 : ℝ)*(upper5) + (480944769250239/12500000000000 : ℝ)*(major0) + (480944769250239/12500000000000 : ℝ)*(major1) + (480944769250239/12500000000000 : ℝ)*(major2) + (1765548579/50000000000000 : ℝ)*(sp3) + (511226895440041/10000000000000 : ℝ)*(sp4) + (639033653993723/12500000000000 : ℝ)*(sp5) + (2556114283158121/50000000000000 : ℝ)*(sp6) + (650896001851063/25000000000000 : ℝ)*(sp7) + (277549373/100000000000000 : ℝ)*(sp8) + (20332816771/50000000000000 : ℝ)*(sp14) + (260358753850141/10000000000000 : ℝ)*(f.failure) + (639033653993723/12500000000000 : ℝ)*(f.sum) + (673708377963/246250000000000000000000000 : ℝ)*base66 + (1606289935279261429/24625000000000000000000000000000 : ℝ)*base67 + (1112440688780261429/24625000000000000000000000000000 : ℝ)*base69 + (231386270982511429/24625000000000000000000000000000 : ℝ)*base71 + (2126796273311/492500000000000000000000000 : ℝ)*base74 + (217211655373011429/24625000000000000000000000000000 : ℝ)*base75 + (181948602232261429/24625000000000000000000000000000 : ℝ)*base77 + (593033016438011429/24625000000000000000000000000000 : ℝ)*base79 + (6855598142469/492500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9697323/1000000000000000000000 : ℝ)*base90 + (9697323/1000000000000000000000 : ℝ)*base92 + (9697323/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59233/100000 : ℝ) ≤ (51053338330599300427862879759079/86187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2633957/5000000000000 : ℝ)*(upper2) + (10104387/20000000000000 : ℝ)*(upper3) + (4385889/20000000000000 : ℝ)*(lower5) + (488786221637209/12500000000000 : ℝ)*(major0) + (488786221637209/12500000000000 : ℝ)*(major1) + (488786221637209/12500000000000 : ℝ)*(major2) + (644349220545953/12500000000000 : ℝ)*(sp0) + (644348683112471/12500000000000 : ℝ)*(sp1) + (2577393178977559/50000000000000 : ℝ)*(sp2) + (1323018259503449/50000000000000 : ℝ)*(sp3) + (7887140821/100000000000000 : ℝ)*(sp5) + (608353321/100000000000000 : ℝ)*(sp7) + (1793836483/50000000000000 : ℝ)*(sp8) + (10994085471/100000000000000 : ℝ)*(sp10) + (2646037127360219/100000000000000 : ℝ)*(f.failure) + (5154797352040589/100000000000000 : ℝ)*(f.sum) + (19186275991199/6895000000000000000000000000 : ℝ)*base66 + (23773035949905307/172375000000000000000000000000000 : ℝ)*base68 + (3659586864940780307/172375000000000000000000000000000 : ℝ)*base70 + (1418029831948844693/172375000000000000000000000000000 : ℝ)*base71 + (11126320588869/1723750000000000000000000000 : ℝ)*base73 + (616961880836655307/172375000000000000000000000000000 : ℝ)*base76 + (530961123465280307/172375000000000000000000000000000 : ℝ)*base78 + (1234239377728219693/172375000000000000000000000000000 : ℝ)*base79 + (7707957531061/1723750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (42457757/10000000000000000000000 : ℝ)*base90 + (42457757/10000000000000000000000 : ℝ)*base92 + (42457757/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39769/50000 : ℝ) ≤ (274214627830737026363049984021921/344750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (385912439/50000000000000 : ℝ)*(upper0) + (19910069/50000000000000 : ℝ)*(lower1) + (30598463/25000000000000 : ℝ)*(upper2) + (95879871/100000000000000 : ℝ)*(lower3) + (138808071/10000000000000 : ℝ)*(lower5) + (2189262214038791/50000000000000 : ℝ)*(major0) + (2189262214038791/50000000000000 : ℝ)*(major1) + (2189262214038791/50000000000000 : ℝ)*(major2) + (78235799307/100000000000000 : ℝ)*(sp1) + (103544465583/100000000000000 : ℝ)*(sp3) + (576765065937421/10000000000000 : ℝ)*(sp8) + (720946552946863/12500000000000 : ℝ)*(sp9) + (576765065937421/10000000000000 : ℝ)*(sp10) + (1481390636390663/50000000000000 : ℝ)*(sp11) + (740721204311727/25000000000000 : ℝ)*(f.failure) + (576765065937421/10000000000000 : ℝ)*(f.sum) + (21844176634149/6895000000000000000000000000 : ℝ)*base66 + (3162444257527107307/689500000000000000000000000000000 : ℝ)*base67 + (9115817184335392693/689500000000000000000000000000000 : ℝ)*base70 + (7176102986525892693/689500000000000000000000000000000 : ℝ)*base72 + (32902141232179/6895000000000000000000000000 : ℝ)*base74 + (5841984128065392693/689500000000000000000000000000000 : ℝ)*base76 + (2924502557425392693/689500000000000000000000000000000 : ℝ)*base78 + (1879811707902107307/689500000000000000000000000000000 : ℝ)*base79 + (19618757259299/6895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (27429481/2500000000000000000000 : ℝ)*base90 + (27429481/2500000000000000000000 : ℝ)*base92 + (27429481/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-82927/100000 : ℝ) ≤ (-71470723595572104876093675185433/86187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186935393/50000000000000 : ℝ)*(lower1) + (157665921/100000000000000 : ℝ)*(lower2) + (32042831/12500000000000 : ℝ)*(upper5) + (551634164989057/12500000000000 : ℝ)*(major0) + (551634164989057/12500000000000 : ℝ)*(major1) + (551634164989057/12500000000000 : ℝ)*(major2) + (23200126161/100000000000000 : ℝ)*(sp0) + (482677727287/100000000000000 : ℝ)*(sp5) + (527547595109/100000000000000 : ℝ)*(sp6) + (73244383233/50000000000000 : ℝ)*(sp7) + (5867501447602753/100000000000000 : ℝ)*(sp12) + (5867041970001627/100000000000000 : ℝ)*(sp13) + (1466749275033451/25000000000000 : ℝ)*(sp14) + (746529267284697/25000000000000 : ℝ)*(sp15) + (1493131778952627/50000000000000 : ℝ)*(f.failure) + (2933762323864457/50000000000000 : ℝ)*(f.sum) + (62805178761207/6895000000000000000000000000 : ℝ)*base66 + (384116769513986811/172375000000000000000000000000000 : ℝ)*base68 + (935277961199111811/172375000000000000000000000000000 : ℝ)*base70 + (306871820133138189/172375000000000000000000000000000 : ℝ)*base71 + (21057434381561/3447500000000000000000000000 : ℝ)*base74 + (1551949195497111811/172375000000000000000000000000000 : ℝ)*base76 + (161204605521111811/172375000000000000000000000000000 : ℝ)*base78 + (1157262463143263189/172375000000000000000000000000000 : ℝ)*base79 + (1653649972367/6895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (23837819/5000000000000000000000 : ℝ)*base89 + (23837819/5000000000000000000000 : ℝ)*base91 + (23837819/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1055_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59233/100000 : ℝ) else (39769/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82927/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1055_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1055_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59233/100000 : ℝ) else (39769/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82927/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1055_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1055_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1055_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59233/100000 : ℝ) else (39769/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82927/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1055_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
