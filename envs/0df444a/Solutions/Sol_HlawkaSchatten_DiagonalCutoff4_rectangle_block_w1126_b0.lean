-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:45.264625+00:00
-- url     : https://prove2.me/submissions/56d76cf6-44ea-4d8c-85a3-c564844d0350

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
theorem support_rectangle_w1126_s0_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1896885069/10000000000 : ℝ)*x 0 + (6058035689/10000000000 : ℝ)*x 1 + (955689059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896885069/10000000000 : ℝ)^8319 ≤ (11022033262811/100000000000000 : ℝ)^6271 := by
    have hnat : (1896885069 : ℕ)^8319*100000000000000^6271 ≤ 11022033262811^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896885069 10000000000 11022033262811 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6058035689/10000000000 : ℝ)^8319 ≤ (12858348153969/25000000000000 : ℝ)^6271 := by
    have hnat : (6058035689 : ℕ)^8319*25000000000000^6271 ≤ 12858348153969^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6058035689 10000000000 12858348153969 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955689059/2000000000 : ℝ)^8319 ≤ (750891481939/2000000000000 : ℝ)^6271 := by
    have hnat : (955689059 : ℕ)^8319*2000000000000^6271 ≤ 750891481939^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955689059 2000000000 750891481939 2000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1896885069/10000000000 : ℝ), (6058035689/10000000000 : ℝ), (955689059/2000000000 : ℝ)] ![(11022033262811/100000000000000 : ℝ), (12858348153969/25000000000000 : ℝ), (750891481939/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1896885069/10000000000 : ℝ)|^8319 ≤ (11022033262811/100000000000000 : ℝ)^6271
        have hw : |(-1896885069/10000000000 : ℝ)|=(1896885069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6058035689/10000000000 : ℝ)|^8319 ≤ (12858348153969/25000000000000 : ℝ)^6271
        have hw : |(6058035689/10000000000 : ℝ)|=(6058035689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955689059/2000000000 : ℝ)|^8319 ≤ (750891481939/2000000000000 : ℝ)^6271
        have hw : |(955689059/2000000000 : ℝ)|=(955689059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s0_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689711871/1250000000 : ℝ)*x 0 + (-328959943/1250000000 : ℝ)*x 1 + (4778445357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689711871/1250000000 : ℝ)^8319 ≤ (45438106066519/100000000000000 : ℝ)^6271 := by
    have hnat : (689711871 : ℕ)^8319*100000000000000^6271 ≤ 45438106066519^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689711871 1250000000 45438106066519 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328959943/1250000000 : ℝ)^8319 ≤ (2127164896103/12500000000000 : ℝ)^6271 := by
    have hnat : (328959943 : ℕ)^8319*12500000000000^6271 ≤ 2127164896103^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328959943 1250000000 2127164896103 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4778445357/10000000000 : ℝ)^8319 ≤ (37544574743179/100000000000000 : ℝ)^6271 := by
    have hnat : (4778445357 : ℕ)^8319*100000000000000^6271 ≤ 37544574743179^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778445357 10000000000 37544574743179 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689711871/1250000000 : ℝ), (-328959943/1250000000 : ℝ), (4778445357/10000000000 : ℝ)] ![(45438106066519/100000000000000 : ℝ), (2127164896103/12500000000000 : ℝ), (37544574743179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689711871/1250000000 : ℝ)|^8319 ≤ (45438106066519/100000000000000 : ℝ)^6271
        have hw : |(689711871/1250000000 : ℝ)|=(689711871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-328959943/1250000000 : ℝ)|^8319 ≤ (2127164896103/12500000000000 : ℝ)^6271
        have hw : |(-328959943/1250000000 : ℝ)|=(328959943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4778445357/10000000000 : ℝ)|^8319 ≤ (37544574743179/100000000000000 : ℝ)^6271
        have hw : |(4778445357/10000000000 : ℝ)|=(4778445357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s0_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (344855931/625000000 : ℝ)*x 0 + (4778445393/10000000000 : ℝ)*x 1 + (-2631679593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344855931/625000000 : ℝ)^8319 ≤ (45438105279963/100000000000000 : ℝ)^6271 := by
    have hnat : (344855931 : ℕ)^8319*100000000000000^6271 ≤ 45438105279963^6271*625000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344855931 625000000 45438105279963 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4778445393/10000000000 : ℝ)^8319 ≤ (37544575118409/100000000000000 : ℝ)^6271 := by
    have hnat : (4778445393 : ℕ)^8319*100000000000000^6271 ≤ 37544575118409^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778445393 10000000000 37544575118409 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631679593/10000000000 : ℝ)^8319 ≤ (531791237161/3125000000000 : ℝ)^6271 := by
    have hnat : (2631679593 : ℕ)^8319*3125000000000^6271 ≤ 531791237161^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631679593 10000000000 531791237161 3125000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344855931/625000000 : ℝ), (4778445393/10000000000 : ℝ), (-2631679593/10000000000 : ℝ)] ![(45438105279963/100000000000000 : ℝ), (37544575118409/100000000000000 : ℝ), (531791237161/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344855931/625000000 : ℝ)|^8319 ≤ (45438105279963/100000000000000 : ℝ)^6271
        have hw : |(344855931/625000000 : ℝ)|=(344855931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4778445393/10000000000 : ℝ)|^8319 ≤ (37544575118409/100000000000000 : ℝ)^6271
        have hw : |(4778445393/10000000000 : ℝ)|=(4778445393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2631679593/10000000000 : ℝ)|^8319 ≤ (531791237161/3125000000000 : ℝ)^6271
        have hw : |(-2631679593/10000000000 : ℝ)|=(2631679593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s0_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1050572007/2500000000 : ℝ)*x 0 + (3121831203/10000000000 : ℝ)*x 1 + (1131911273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050572007/2500000000 : ℝ)^8319 ≤ (7915216758467/25000000000000 : ℝ)^6271 := by
    have hnat : (1050572007 : ℕ)^8319*25000000000000^6271 ≤ 7915216758467^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050572007 2500000000 7915216758467 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121831203/10000000000 : ℝ)^8319 ≤ (21344809762479/100000000000000 : ℝ)^6271 := by
    have hnat : (3121831203 : ℕ)^8319*100000000000000^6271 ≤ 21344809762479^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121831203 10000000000 21344809762479 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131911273/2000000000 : ℝ)^8319 ≤ (46994323181899/100000000000000 : ℝ)^6271 := by
    have hnat : (1131911273 : ℕ)^8319*100000000000000^6271 ≤ 46994323181899^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131911273 2000000000 46994323181899 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050572007/2500000000 : ℝ), (3121831203/10000000000 : ℝ), (1131911273/2000000000 : ℝ)] ![(7915216758467/25000000000000 : ℝ), (21344809762479/100000000000000 : ℝ), (46994323181899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050572007/2500000000 : ℝ)|^8319 ≤ (7915216758467/25000000000000 : ℝ)^6271
        have hw : |(1050572007/2500000000 : ℝ)|=(1050572007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121831203/10000000000 : ℝ)|^8319 ≤ (21344809762479/100000000000000 : ℝ)^6271
        have hw : |(3121831203/10000000000 : ℝ)|=(3121831203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131911273/2000000000 : ℝ)|^8319 ≤ (46994323181899/100000000000000 : ℝ)^6271
        have hw : |(1131911273/2000000000 : ℝ)|=(1131911273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s0_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-23775973/125000000 : ℝ)*x 0 + (601432859/1250000000 : ℝ)*x 1 + (6023858531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23775973/125000000 : ℝ)^8319 ≤ (2212415650143/20000000000000 : ℝ)^6271 := by
    have hnat : (23775973 : ℕ)^8319*20000000000000^6271 ≤ 2212415650143^6271*125000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23775973 125000000 2212415650143 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601432859/1250000000 : ℝ)^8319 ≤ (37889105699739/100000000000000 : ℝ)^6271 := by
    have hnat : (601432859 : ℕ)^8319*100000000000000^6271 ≤ 37889105699739^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601432859 1250000000 37889105699739 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6023858531/10000000000 : ℝ)^8319 ≤ (51048816032339/100000000000000 : ℝ)^6271 := by
    have hnat : (6023858531 : ℕ)^8319*100000000000000^6271 ≤ 51048816032339^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6023858531 10000000000 51048816032339 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23775973/125000000 : ℝ), (601432859/1250000000 : ℝ), (6023858531/10000000000 : ℝ)] ![(2212415650143/20000000000000 : ℝ), (37889105699739/100000000000000 : ℝ), (51048816032339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23775973/125000000 : ℝ)|^8319 ≤ (2212415650143/20000000000000 : ℝ)^6271
        have hw : |(-23775973/125000000 : ℝ)|=(23775973/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601432859/1250000000 : ℝ)|^8319 ≤ (37889105699739/100000000000000 : ℝ)^6271
        have hw : |(601432859/1250000000 : ℝ)|=(601432859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6023858531/10000000000 : ℝ)|^8319 ≤ (51048816032339/100000000000000 : ℝ)^6271
        have hw : |(6023858531/10000000000 : ℝ)|=(6023858531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s0_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170081353/10000000000 : ℝ)*x 0 + (-693133233/5000000000 : ℝ)*x 1 + (3011929231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170081353/10000000000 : ℝ)^8319 ≤ (41680275586593/100000000000000 : ℝ)^6271 := by
    have hnat : (5170081353 : ℕ)^8319*100000000000000^6271 ≤ 41680275586593^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170081353 10000000000 41680275586593 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693133233/5000000000 : ℝ)^8319 ≤ (36354545657/500000000000 : ℝ)^6271 := by
    have hnat : (693133233 : ℕ)^8319*500000000000^6271 ≤ 36354545657^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693133233 5000000000 36354545657 500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3011929231/5000000000 : ℝ)^8319 ≤ (25524407628319/50000000000000 : ℝ)^6271 := by
    have hnat : (3011929231 : ℕ)^8319*50000000000000^6271 ≤ 25524407628319^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011929231 5000000000 25524407628319 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170081353/10000000000 : ℝ), (-693133233/5000000000 : ℝ), (3011929231/5000000000 : ℝ)] ![(41680275586593/100000000000000 : ℝ), (36354545657/500000000000 : ℝ), (25524407628319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170081353/10000000000 : ℝ)|^8319 ≤ (41680275586593/100000000000000 : ℝ)^6271
        have hw : |(5170081353/10000000000 : ℝ)|=(5170081353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-693133233/5000000000 : ℝ)|^8319 ≤ (36354545657/500000000000 : ℝ)^6271
        have hw : |(-693133233/5000000000 : ℝ)|=(693133233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3011929231/5000000000 : ℝ)|^8319 ≤ (25524407628319/50000000000000 : ℝ)^6271
        have hw : |(3011929231/5000000000 : ℝ)|=(3011929231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s0_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170081383/10000000000 : ℝ)*x 0 + (6023858451/10000000000 : ℝ)*x 1 + (-34656661/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170081383/10000000000 : ℝ)^8319 ≤ (41680275907433/100000000000000 : ℝ)^6271 := by
    have hnat : (5170081383 : ℕ)^8319*100000000000000^6271 ≤ 41680275907433^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170081383 10000000000 41680275907433 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6023858451/10000000000 : ℝ)^8319 ≤ (3190550945811/6250000000000 : ℝ)^6271 := by
    have hnat : (6023858451 : ℕ)^8319*6250000000000^6271 ≤ 3190550945811^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6023858451 10000000000 3190550945811 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34656661/250000000 : ℝ)^8319 ≤ (227215904703/3125000000000 : ℝ)^6271 := by
    have hnat : (34656661 : ℕ)^8319*3125000000000^6271 ≤ 227215904703^6271*250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34656661 250000000 227215904703 3125000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170081383/10000000000 : ℝ), (6023858451/10000000000 : ℝ), (-34656661/250000000 : ℝ)] ![(41680275907433/100000000000000 : ℝ), (3190550945811/6250000000000 : ℝ), (227215904703/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170081383/10000000000 : ℝ)|^8319 ≤ (41680275907433/100000000000000 : ℝ)^6271
        have hw : |(5170081383/10000000000 : ℝ)|=(5170081383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6023858451/10000000000 : ℝ)|^8319 ≤ (3190550945811/6250000000000 : ℝ)^6271
        have hw : |(6023858451/10000000000 : ℝ)|=(6023858451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34656661/250000000 : ℝ)|^8319 ≤ (227215904703/3125000000000 : ℝ)^6271
        have hw : |(-34656661/250000000 : ℝ)|=(34656661/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s0_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2106293339/5000000000 : ℝ)*x 0 + (699259353/1250000000 : ℝ)*x 1 + (398701579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106293339/5000000000 : ℝ)^8319 ≤ (15881920243527/50000000000000 : ℝ)^6271 := by
    have hnat : (2106293339 : ℕ)^8319*50000000000000^6271 ≤ 15881920243527^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106293339 5000000000 15881920243527 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (699259353/1250000000 : ℝ)^8319 ≤ (4627438900201/10000000000000 : ℝ)^6271 := by
    have hnat : (699259353 : ℕ)^8319*10000000000000^6271 ≤ 4627438900201^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699259353 1250000000 4627438900201 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398701579/1250000000 : ℝ)^8319 ≤ (21961770499277/100000000000000 : ℝ)^6271 := by
    have hnat : (398701579 : ℕ)^8319*100000000000000^6271 ≤ 21961770499277^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398701579 1250000000 21961770499277 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106293339/5000000000 : ℝ), (699259353/1250000000 : ℝ), (398701579/1250000000 : ℝ)] ![(15881920243527/50000000000000 : ℝ), (4627438900201/10000000000000 : ℝ), (21961770499277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106293339/5000000000 : ℝ)|^8319 ≤ (15881920243527/50000000000000 : ℝ)^6271
        have hw : |(2106293339/5000000000 : ℝ)|=(2106293339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(699259353/1250000000 : ℝ)|^8319 ≤ (4627438900201/10000000000000 : ℝ)^6271
        have hw : |(699259353/1250000000 : ℝ)|=(699259353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398701579/1250000000 : ℝ)|^8319 ≤ (21961770499277/100000000000000 : ℝ)^6271
        have hw : |(398701579/1250000000 : ℝ)|=(398701579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27877/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4159/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4159 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4159*1^1024 ≤ 0^1024*1^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4159/1024 : ℝ) ≤ (2419676619459905661/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4159 ≤ (2419676619459905661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4159*100000000000000000000^1024 ≤ 2419676619459905661^1024*5^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2419676619459905661 100000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2419676619459905661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4159 := by
      have hnat : (1 : ℕ)^1024*1^4159 ≤ 1^4159*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102419676619459905661/100000000000000000000 : ℝ) ≤ (628689990338099/625000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (102419676619459905661/100000000000000000000 : ℝ)^1024 ≤ (628689990338099/625000000000000 : ℝ)^4159 := by
      have hnat : (102419676619459905661 : ℕ)^1024*625000000000000^4159 ≤ 628689990338099^4159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102419676619459905661 100000000000000000000 628689990338099 625000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628689990338099/625000000000000 : ℝ)) (X := (102419676619459905661/100000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52419676619459905661/50000000000000000000 : ℝ) ≤ (316189990338099/312500000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (52419676619459905661/50000000000000000000 : ℝ)^1024 ≤ (316189990338099/312500000000000 : ℝ)^4159 := by
      have hnat : (52419676619459905661 : ℕ)^1024*312500000000000^4159 ≤ 316189990338099^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52419676619459905661 50000000000000000000 316189990338099 312500000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (316189990338099/312500000000000 : ℝ)) (X := (52419676619459905661/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3689990338099/250000000000000 : ℝ)*(0 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3689990338099/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2419676619459905661/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3689990338099/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3689990338099/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(628689990338099/625000000000000 : ℝ) by norm_num, show 1+(2419676619459905661/100000000000000000000 : ℝ)+(0 : ℝ)=(102419676619459905661/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2419676619459905661/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3689990338099/250000000000000 : ℝ)*(2/5 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3689990338099/250000000000000 : ℝ)*(2/5 : ℝ)=(316189990338099/312500000000000 : ℝ) by norm_num, show 1+2*(2419676619459905661/100000000000000000000 : ℝ)=(52419676619459905661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3689990338099/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3689990338099/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3689990338099/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3689990338099/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3689990338099/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3689990338099/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1896885069/10000000000 : ℝ)*X 0 0+(6058035689/10000000000 : ℝ)*X 0 1+(955689059/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689711871/1250000000 : ℝ)*X 1 0+(-328959943/1250000000 : ℝ)*X 1 1+(4778445357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344855931/625000000 : ℝ)*X 2 0+(4778445393/10000000000 : ℝ)*X 2 1+(-2631679593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050572007/2500000000 : ℝ)*X 0 0+(3121831203/10000000000 : ℝ)*X 0 1+(1131911273/2000000000 : ℝ)*X 0 2+(1050572007/2500000000 : ℝ)*X 1 0+(3121831203/10000000000 : ℝ)*X 1 1+(1131911273/2000000000 : ℝ)*X 1 2+(1050572007/2500000000 : ℝ)*X 2 0+(3121831203/10000000000 : ℝ)*X 2 1+(1131911273/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-23775973/125000000 : ℝ)*X 0 0+(601432859/1250000000 : ℝ)*X 0 1+(6023858531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170081353/10000000000 : ℝ)*X 1 0+(-693133233/5000000000 : ℝ)*X 1 1+(3011929231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170081383/10000000000 : ℝ)*X 2 0+(6023858451/10000000000 : ℝ)*X 2 1+(-34656661/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2106293339/5000000000 : ℝ)*X 0 0+(699259353/1250000000 : ℝ)*X 0 1+(398701579/1250000000 : ℝ)*X 0 2+(2106293339/5000000000 : ℝ)*X 1 0+(699259353/1250000000 : ℝ)*X 1 1+(398701579/1250000000 : ℝ)*X 1 2+(2106293339/5000000000 : ℝ)*X 2 0+(699259353/1250000000 : ℝ)*X 2 1+(398701579/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3639709578998501265399/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2395263/3125000000000 : ℝ)*(base1) + (1828420507/100000000000000 : ℝ)*(base19) + (339316321/20000000000000 : ℝ)*(base23) + (121641057/100000000000000 : ℝ)*(base24) + (84102227/20000000000000 : ℝ)*(upper3) + (117556932880433/20000000000000 : ℝ)*(major0) + (117556932880433/20000000000000 : ℝ)*(major1) + (117556932880433/20000000000000 : ℝ)*(major2) + (48844138881997/6250000000000 : ℝ)*(sp0) + (12211067988593/1562500000000 : ℝ)*(sp1) + (781508361467797/100000000000000 : ℝ)*(sp2) + (49256950785563/12500000000000 : ℝ)*(sp3) + (2017113461/50000000000000 : ℝ)*(sp4) + (1611766821/50000000000000 : ℝ)*(sp7) + (197029453233281/50000000000000 : ℝ)*(f.failure) + (390755089845229/50000000000000 : ℝ)*(f.sum) + (834895966867/2500000000000000000000000000 : ℝ)*base65 + (14880100356867/5000000000000000000000000000 : ℝ)*base67 + (25958255886867/5000000000000000000000000000 : ℝ)*base69 + (2139906896867/5000000000000000000000000000 : ℝ)*base71 + (1886747936867/2500000000000000000000000000 : ℝ)*base73 + (404378676867/5000000000000000000000000000 : ℝ)*base75 + (22063594016867/5000000000000000000000000000 : ℝ)*base77 + (8605971188133/5000000000000000000000000000 : ℝ)*base80 + (15608943809367/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (648957/625000000000000000000 : ℝ)*base90 + (648957/625000000000000000000 : ℝ)*base92 + (648957/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107655747172933948086441/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12566637/12500000000000 : ℝ)*(base1) + (2124370221/100000000000000 : ℝ)*(base19) + (2128697453/100000000000000 : ℝ)*(base23) + (23652103/10000000000000 : ℝ)*(upper3) + (245282893/100000000000000 : ℝ)*(upper5) + (620353494617153/100000000000000 : ℝ)*(major0) + (620353494617153/100000000000000 : ℝ)*(major1) + (620353494617153/100000000000000 : ℝ)*(major2) + (2175614301/50000000000000 : ℝ)*(sp1) + (4344405659/100000000000000 : ℝ)*(sp2) + (824813305429599/100000000000000 : ℝ)*(sp4) + (824806729297679/100000000000000 : ℝ)*(sp5) + (82480673179339/10000000000000 : ℝ)*(sp6) + (103973349180677/25000000000000 : ℝ)*(sp7) + (103973374313951/25000000000000 : ℝ)*(f.failure) + (824813204896503/100000000000000 : ℝ)*(f.sum) + (36538811512147/12500000000000000000000000000 : ℝ)*base65 + (168681258187853/25000000000000000000000000000 : ℝ)*base68 + (90277628312853/25000000000000000000000000000 : ℝ)*base70 + (8624073637147/25000000000000000000000000000 : ℝ)*base71 + (1068133812853/12500000000000000000000000000 : ℝ)*base74 + (187783583112147/25000000000000000000000000000 : ℝ)*base75 + (13571063362147/25000000000000000000000000000 : ℝ)*base77 + (111450496912853/25000000000000000000000000000 : ℝ)*base80 + (39964953550353/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (997947/312500000000000000000 : ℝ)*base90 + (997947/312500000000000000000 : ℝ)*base92 + (997947/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1126_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27877/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1126_s1_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102700729/10000000000 : ℝ)*x 0 + (2852910629/5000000000 : ℝ)*x 1 + (4998889919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102700729/10000000000 : ℝ)^8319 ≤ (2527192413131/20000000000000 : ℝ)^6271 := by
    have hnat : (2102700729 : ℕ)^8319*20000000000000^6271 ≤ 2527192413131^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102700729 10000000000 2527192413131 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852910629/5000000000 : ℝ)^8319 ≤ (1900185002451/4000000000000 : ℝ)^6271 := by
    have hnat : (2852910629 : ℕ)^8319*4000000000000^6271 ≤ 1900185002451^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852910629 5000000000 1900185002451 4000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998889919/10000000000 : ℝ)^8319 ≤ (19929706427681/50000000000000 : ℝ)^6271 := by
    have hnat : (4998889919 : ℕ)^8319*50000000000000^6271 ≤ 19929706427681^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998889919 10000000000 19929706427681 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102700729/10000000000 : ℝ), (2852910629/5000000000 : ℝ), (4998889919/10000000000 : ℝ)] ![(2527192413131/20000000000000 : ℝ), (1900185002451/4000000000000 : ℝ), (19929706427681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102700729/10000000000 : ℝ)|^8319 ≤ (2527192413131/20000000000000 : ℝ)^6271
        have hw : |(-2102700729/10000000000 : ℝ)|=(2102700729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2852910629/5000000000 : ℝ)|^8319 ≤ (1900185002451/4000000000000 : ℝ)^6271
        have hw : |(2852910629/5000000000 : ℝ)|=(2852910629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998889919/10000000000 : ℝ)|^8319 ≤ (19929706427681/50000000000000 : ℝ)^6271
        have hw : |(4998889919/10000000000 : ℝ)|=(4998889919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s1_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67750067/125000000 : ℝ)*x 0 + (-155282091/625000000 : ℝ)*x 1 + (624861197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67750067/125000000 : ℝ)^8319 ≤ (5546750648641/12500000000000 : ℝ)^6271 := by
    have hnat : (67750067 : ℕ)^8319*12500000000000^6271 ≤ 5546750648641^6271*125000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67750067 125000000 5546750648641 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155282091/625000000 : ℝ)^8319 ≤ (15766585572257/100000000000000 : ℝ)^6271 := by
    have hnat : (155282091 : ℕ)^8319*100000000000000^6271 ≤ 15766585572257^6271*625000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155282091 625000000 15766585572257 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624861197/1250000000 : ℝ)^8319 ≤ (39859409227207/100000000000000 : ℝ)^6271 := by
    have hnat : (624861197 : ℕ)^8319*100000000000000^6271 ≤ 39859409227207^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624861197 1250000000 39859409227207 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67750067/125000000 : ℝ), (-155282091/625000000 : ℝ), (624861197/1250000000 : ℝ)] ![(5546750648641/12500000000000 : ℝ), (15766585572257/100000000000000 : ℝ), (39859409227207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67750067/125000000 : ℝ)|^8319 ≤ (5546750648641/12500000000000 : ℝ)^6271
        have hw : |(67750067/125000000 : ℝ)|=(67750067/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155282091/625000000 : ℝ)|^8319 ≤ (15766585572257/100000000000000 : ℝ)^6271
        have hw : |(-155282091/625000000 : ℝ)|=(155282091/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(624861197/1250000000 : ℝ)|^8319 ≤ (39859409227207/100000000000000 : ℝ)^6271
        have hw : |(624861197/1250000000 : ℝ)|=(624861197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s1_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355001749/2500000000 : ℝ)*x 0 + (4998888093/10000000000 : ℝ)*x 1 + (-310564151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355001749/2500000000 : ℝ)^8319 ≤ (8874804591491/20000000000000 : ℝ)^6271 := by
    have hnat : (1355001749 : ℕ)^8319*20000000000000^6271 ≤ 8874804591491^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355001749 2500000000 8874804591491 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4998888093/10000000000 : ℝ)^8319 ≤ (7971878708093/20000000000000 : ℝ)^6271 := by
    have hnat : (4998888093 : ℕ)^8319*20000000000000^6271 ≤ 7971878708093^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998888093 10000000000 7971878708093 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310564151/1250000000 : ℝ)^8319 ≤ (15766583484489/100000000000000 : ℝ)^6271 := by
    have hnat : (310564151 : ℕ)^8319*100000000000000^6271 ≤ 15766583484489^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310564151 1250000000 15766583484489 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355001749/2500000000 : ℝ), (4998888093/10000000000 : ℝ), (-310564151/1250000000 : ℝ)] ![(8874804591491/20000000000000 : ℝ), (7971878708093/20000000000000 : ℝ), (15766583484489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355001749/2500000000 : ℝ)|^8319 ≤ (8874804591491/20000000000000 : ℝ)^6271
        have hw : |(1355001749/2500000000 : ℝ)|=(1355001749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4998888093/10000000000 : ℝ)|^8319 ≤ (7971878708093/20000000000000 : ℝ)^6271
        have hw : |(4998888093/10000000000 : ℝ)|=(4998888093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310564151/1250000000 : ℝ)|^8319 ≤ (15766583484489/100000000000000 : ℝ)^6271
        have hw : |(-310564151/1250000000 : ℝ)|=(310564151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s1_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (431878651/1000000000 : ℝ)*x 0 + (3673997431/10000000000 : ℝ)*x 1 + (5076004679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431878651/1000000000 : ℝ)^8319 ≤ (8207619272741/25000000000000 : ℝ)^6271 := by
    have hnat : (431878651 : ℕ)^8319*25000000000000^6271 ≤ 8207619272741^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431878651 1000000000 8207619272741 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3673997431/10000000000 : ℝ)^8319 ≤ (26492364820617/100000000000000 : ℝ)^6271 := by
    have hnat : (3673997431 : ℕ)^8319*100000000000000^6271 ≤ 26492364820617^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3673997431 10000000000 26492364820617 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076004679/10000000000 : ℝ)^8319 ≤ (40677158074331/100000000000000 : ℝ)^6271 := by
    have hnat : (5076004679 : ℕ)^8319*100000000000000^6271 ≤ 40677158074331^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076004679 10000000000 40677158074331 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431878651/1000000000 : ℝ), (3673997431/10000000000 : ℝ), (5076004679/10000000000 : ℝ)] ![(8207619272741/25000000000000 : ℝ), (26492364820617/100000000000000 : ℝ), (40677158074331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431878651/1000000000 : ℝ)|^8319 ≤ (8207619272741/25000000000000 : ℝ)^6271
        have hw : |(431878651/1000000000 : ℝ)|=(431878651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3673997431/10000000000 : ℝ)|^8319 ≤ (26492364820617/100000000000000 : ℝ)^6271
        have hw : |(3673997431/10000000000 : ℝ)|=(3673997431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076004679/10000000000 : ℝ)|^8319 ≤ (40677158074331/100000000000000 : ℝ)^6271
        have hw : |(5076004679/10000000000 : ℝ)|=(5076004679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s1_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-525882421/2500000000 : ℝ)*x 0 + (5008601937/10000000000 : ℝ)*x 1 + (569591571/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525882421/2500000000 : ℝ)^8319 ≤ (12642570888059/100000000000000 : ℝ)^6271 := by
    have hnat : (525882421 : ℕ)^8319*100000000000000^6271 ≤ 12642570888059^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525882421 2500000000 12642570888059 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5008601937/10000000000 : ℝ)^8319 ≤ (39962176340189/100000000000000 : ℝ)^6271 := by
    have hnat : (5008601937 : ℕ)^8319*100000000000000^6271 ≤ 39962176340189^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008601937 10000000000 39962176340189 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569591571/1000000000 : ℝ)^8319 ≤ (47395252751781/100000000000000 : ℝ)^6271 := by
    have hnat : (569591571 : ℕ)^8319*100000000000000^6271 ≤ 47395252751781^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569591571 1000000000 47395252751781 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525882421/2500000000 : ℝ), (5008601937/10000000000 : ℝ), (569591571/1000000000 : ℝ)] ![(12642570888059/100000000000000 : ℝ), (39962176340189/100000000000000 : ℝ), (47395252751781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525882421/2500000000 : ℝ)|^8319 ≤ (12642570888059/100000000000000 : ℝ)^6271
        have hw : |(-525882421/2500000000 : ℝ)|=(525882421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5008601937/10000000000 : ℝ)|^8319 ≤ (39962176340189/100000000000000 : ℝ)^6271
        have hw : |(5008601937/10000000000 : ℝ)|=(5008601937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569591571/1000000000 : ℝ)|^8319 ≤ (47395252751781/100000000000000 : ℝ)^6271
        have hw : |(569591571/1000000000 : ℝ)|=(569591571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s1_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (654863349/1250000000 : ℝ)*x 0 + (-1787486951/10000000000 : ℝ)*x 1 + (1139183093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654863349/1250000000 : ℝ)^8319 ≤ (8483587293713/20000000000000 : ℝ)^6271 := by
    have hnat : (654863349 : ℕ)^8319*20000000000000^6271 ≤ 8483587293713^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654863349 1250000000 8483587293713 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1787486951/10000000000 : ℝ)^8319 ≤ (5093406738479/50000000000000 : ℝ)^6271 := by
    have hnat : (1787486951 : ℕ)^8319*50000000000000^6271 ≤ 5093406738479^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787486951 10000000000 5093406738479 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139183093/2000000000 : ℝ)^8319 ≤ (2962203127961/6250000000000 : ℝ)^6271 := by
    have hnat : (1139183093 : ℕ)^8319*6250000000000^6271 ≤ 2962203127961^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139183093 2000000000 2962203127961 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654863349/1250000000 : ℝ), (-1787486951/10000000000 : ℝ), (1139183093/2000000000 : ℝ)] ![(8483587293713/20000000000000 : ℝ), (5093406738479/50000000000000 : ℝ), (2962203127961/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654863349/1250000000 : ℝ)|^8319 ≤ (8483587293713/20000000000000 : ℝ)^6271
        have hw : |(654863349/1250000000 : ℝ)|=(654863349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1787486951/10000000000 : ℝ)|^8319 ≤ (5093406738479/50000000000000 : ℝ)^6271
        have hw : |(-1787486951/10000000000 : ℝ)|=(1787486951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139183093/2000000000 : ℝ)|^8319 ≤ (2962203127961/6250000000000 : ℝ)^6271
        have hw : |(1139183093/2000000000 : ℝ)|=(1139183093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s1_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327431677/625000000 : ℝ)*x 0 + (569591563/1000000000 : ℝ)*x 1 + (-1787486653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327431677/625000000 : ℝ)^8319 ≤ (42417936898203/100000000000000 : ℝ)^6271 := by
    have hnat : (327431677 : ℕ)^8319*100000000000000^6271 ≤ 42417936898203^6271*625000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327431677 625000000 42417936898203 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569591563/1000000000 : ℝ)^8319 ≤ (4739525186871/10000000000000 : ℝ)^6271 := by
    have hnat : (569591563 : ℕ)^8319*10000000000000^6271 ≤ 4739525186871^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569591563 1000000000 4739525186871 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1787486653/10000000000 : ℝ)^8319 ≤ (2546702806009/25000000000000 : ℝ)^6271 := by
    have hnat : (1787486653 : ℕ)^8319*25000000000000^6271 ≤ 2546702806009^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787486653 10000000000 2546702806009 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327431677/625000000 : ℝ), (569591563/1000000000 : ℝ), (-1787486653/10000000000 : ℝ)] ![(42417936898203/100000000000000 : ℝ), (4739525186871/10000000000000 : ℝ), (2546702806009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327431677/625000000 : ℝ)|^8319 ≤ (42417936898203/100000000000000 : ℝ)^6271
        have hw : |(327431677/625000000 : ℝ)|=(327431677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569591563/1000000000 : ℝ)|^8319 ≤ (4739525186871/10000000000000 : ℝ)^6271
        have hw : |(569591563/1000000000 : ℝ)|=(569591563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1787486653/10000000000 : ℝ)|^8319 ≤ (2546702806009/25000000000000 : ℝ)^6271
        have hw : |(-1787486653/10000000000 : ℝ)|=(1787486653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s1_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4320427849/10000000000 : ℝ)*x 0 + (1011348861/2000000000 : ℝ)*x 1 + (3693641391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320427849/10000000000 : ℝ)^8319 ≤ (16423515013153/50000000000000 : ℝ)^6271 := by
    have hnat : (4320427849 : ℕ)^8319*50000000000000^6271 ≤ 16423515013153^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320427849 10000000000 16423515013153 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011348861/2000000000 : ℝ)^8319 ≤ (40472533291991/100000000000000 : ℝ)^6271 := by
    have hnat : (1011348861 : ℕ)^8319*100000000000000^6271 ≤ 40472533291991^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011348861 2000000000 40472533291991 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3693641391/10000000000 : ℝ)^8319 ≤ (26680436670999/100000000000000 : ℝ)^6271 := by
    have hnat : (3693641391 : ℕ)^8319*100000000000000^6271 ≤ 26680436670999^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693641391 10000000000 26680436670999 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320427849/10000000000 : ℝ), (1011348861/2000000000 : ℝ), (3693641391/10000000000 : ℝ)] ![(16423515013153/50000000000000 : ℝ), (40472533291991/100000000000000 : ℝ), (26680436670999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320427849/10000000000 : ℝ)|^8319 ≤ (16423515013153/50000000000000 : ℝ)^6271
        have hw : |(4320427849/10000000000 : ℝ)|=(4320427849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011348861/2000000000 : ℝ)|^8319 ≤ (40472533291991/100000000000000 : ℝ)^6271
        have hw : |(1011348861/2000000000 : ℝ)|=(1011348861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3693641391/10000000000 : ℝ)|^8319 ≤ (26680436670999/100000000000000 : ℝ)^6271
        have hw : |(3693641391/10000000000 : ℝ)|=(3693641391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5559/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2051/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (347/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (10232706399/100000000000000000000 : ℝ) := by
    have hpowers : (347/100000 : ℝ)^4159 ≤ (10232706399/100000000000000000000 : ℝ)^1024 := by
      have hnat : (347 : ℕ)^4159*100000000000000000000^1024 ≤ 10232706399^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        347 100000 10232706399 100000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (347/100000 : ℝ)) (X := (10232706399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27877/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (558282184828867253/100000000000000000000 : ℝ) := by
    have hpowers : (27877/100000 : ℝ)^4159 ≤ (558282184828867253/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27877 : ℕ)^4159*100000000000000000000^1024 ≤ 558282184828867253^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27877 100000 558282184828867253 100000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27877/100000 : ℝ)) (X := (558282184828867253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000010232706399/50000000000000000000 : ℝ) ≤ (5000000000251943/5000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (50000000010232706399/50000000000000000000 : ℝ)^1024 ≤ (5000000000251943/5000000000000000 : ℝ)^4159 := by
      have hnat : (50000000010232706399 : ℕ)^1024*5000000000000000^4159 ≤ 5000000000251943^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000010232706399 50000000000000000000 5000000000251943 5000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000251943/5000000000000000 : ℝ)) (X := (50000000010232706399/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25139570548765393413/25000000000000000000 : ℝ) ≤ (500685840331759/500000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (25139570548765393413/25000000000000000000 : ℝ)^1024 ≤ (500685840331759/500000000000000 : ℝ)^4159 := by
      have hnat : (25139570548765393413 : ℕ)^1024*500000000000000^4159 ≤ 500685840331759^4159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25139570548765393413 25000000000000000000 500685840331759 500000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500685840331759/500000000000000 : ℝ)) (X := (25139570548765393413/25000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50558282184828867253/50000000000000000000 : ℝ) ≤ (5013716806383237/5000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (50558282184828867253/50000000000000000000 : ℝ)^1024 ≤ (5013716806383237/5000000000000000 : ℝ)^4159 := by
      have hnat : (50558282184828867253 : ℕ)^1024*5000000000000000^4159 ≤ 5013716806383237^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50558282184828867253 50000000000000000000 5013716806383237 5000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013716806383237/5000000000000000 : ℝ)) (X := (50558282184828867253/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10232706399/100000000000000000000 : ℝ) ≤ ((34411310068802107943/34412500000000000000 : ℝ)+2*(6858403065647/1376500000000000 : ℝ)*(347/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (34411310068802107943/34412500000000000000 : ℝ)+2*(6858403065647/1376500000000000 : ℝ)*(347/100000 : ℝ)=(5000000000251943/5000000000000000 : ℝ) by norm_num, show 1+2*(10232706399/100000000000000000000 : ℝ)=(50000000010232706399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(558282184828867253/100000000000000000000 : ℝ)+(10232706399/100000000000000000000 : ℝ) ≤ ((34411310068802107943/34412500000000000000 : ℝ)+(6858403065647/1376500000000000 : ℝ)*((27877/100000 : ℝ)+(347/100000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (34411310068802107943/34412500000000000000 : ℝ)+(6858403065647/1376500000000000 : ℝ)*((27877/100000 : ℝ)+(347/100000 : ℝ))=(500685840331759/500000000000000 : ℝ) by norm_num, show 1+(558282184828867253/100000000000000000000 : ℝ)+(10232706399/100000000000000000000 : ℝ)=(25139570548765393413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(558282184828867253/100000000000000000000 : ℝ) ≤ ((34411310068802107943/34412500000000000000 : ℝ)+2*(6858403065647/1376500000000000 : ℝ)*(27877/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (34411310068802107943/34412500000000000000 : ℝ)+2*(6858403065647/1376500000000000 : ℝ)*(27877/100000 : ℝ)=(5013716806383237/5000000000000000 : ℝ) by norm_num, show 1+2*(558282184828867253/100000000000000000000 : ℝ)=(50558282184828867253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34411310068802107943/34412500000000000000 : ℝ)*(X 1 0+X 2 0)+(6858403065647/1376500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (347/100000 : ℝ)) (hi := (27877/100000 : ℝ)) (c := (34411310068802107943/34412500000000000000 : ℝ)) (alpha := (6858403065647/1376500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34411310068802107943/34412500000000000000 : ℝ)*(X 0 1+X 2 1)+(6858403065647/1376500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (347/100000 : ℝ)) (hi := (27877/100000 : ℝ)) (c := (34411310068802107943/34412500000000000000 : ℝ)) (alpha := (6858403065647/1376500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34411310068802107943/34412500000000000000 : ℝ)*(X 0 2+X 1 2)+(6858403065647/1376500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (347/100000 : ℝ)) (hi := (27877/100000 : ℝ)) (c := (34411310068802107943/34412500000000000000 : ℝ)) (alpha := (6858403065647/1376500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2102700729/10000000000 : ℝ)*X 0 0+(2852910629/5000000000 : ℝ)*X 0 1+(4998889919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((67750067/125000000 : ℝ)*X 1 0+(-155282091/625000000 : ℝ)*X 1 1+(624861197/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355001749/2500000000 : ℝ)*X 2 0+(4998888093/10000000000 : ℝ)*X 2 1+(-310564151/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431878651/1000000000 : ℝ)*X 0 0+(3673997431/10000000000 : ℝ)*X 0 1+(5076004679/10000000000 : ℝ)*X 0 2+(431878651/1000000000 : ℝ)*X 1 0+(3673997431/10000000000 : ℝ)*X 1 1+(5076004679/10000000000 : ℝ)*X 1 2+(431878651/1000000000 : ℝ)*X 2 0+(3673997431/10000000000 : ℝ)*X 2 1+(5076004679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-525882421/2500000000 : ℝ)*X 0 0+(5008601937/10000000000 : ℝ)*X 0 1+(569591571/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((654863349/1250000000 : ℝ)*X 1 0+(-1787486951/10000000000 : ℝ)*X 1 1+(1139183093/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327431677/625000000 : ℝ)*X 2 0+(569591563/1000000000 : ℝ)*X 2 1+(-1787486653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320427849/10000000000 : ℝ)*X 0 0+(1011348861/2000000000 : ℝ)*X 0 1+(3693641391/10000000000 : ℝ)*X 0 2+(4320427849/10000000000 : ℝ)*X 1 0+(1011348861/2000000000 : ℝ)*X 1 1+(3693641391/10000000000 : ℝ)*X 1 2+(4320427849/10000000000 : ℝ)*X 2 0+(1011348861/2000000000 : ℝ)*X 2 1+(3693641391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6201133295922625600583251599/860312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11982401/3125000000000 : ℝ)*(base1) + (155553137/12500000000000 : ℝ)*(base19) + (1671405673/100000000000000 : ℝ)*(base23) + (7125181/100000000000000 : ℝ)*(upper3) + (104031351/50000000000000 : ℝ)*(upper5) + (531959542510877/50000000000000 : ℝ)*(major0) + (531959542510877/50000000000000 : ℝ)*(major1) + (531959542510877/50000000000000 : ℝ)*(major2) + (1414566975701761/100000000000000 : ℝ)*(sp0) + (707285364135157/50000000000000 : ℝ)*(sp1) + (1414570301289737/100000000000000 : ℝ)*(sp2) + (5572379082751/781250000000 : ℝ)*(sp3) + (5380430481/100000000000000 : ℝ)*(sp4) + (1051052437/100000000000000 : ℝ)*(sp7) + (713265957081397/100000000000000 : ℝ)*(f.failure) + (141457197269541/10000000000000 : ℝ)*(f.sum) + (14999457935419/34412500000000000000000000000 : ℝ)*base65 + (16619488340123928989/1720625000000000000000000000000000 : ℝ)*base68 + (6575286838548928989/1720625000000000000000000000000000 : ℝ)*base70 + (5425227429052053989/1720625000000000000000000000000000 : ℝ)*base72 + (345859209604087/68825000000000000000000000000 : ℝ)*base74 + (1173630691820803989/1720625000000000000000000000000000 : ℝ)*base76 + (184405012824553989/1720625000000000000000000000000000 : ℝ)*base78 + (3577365068260178989/1720625000000000000000000000000000 : ℝ)*base80 + (159291236157637/68825000000000000000000000000 : ℝ)*base82 + (9588591/1250000000000000000000 : ℝ)*base89 + (9588591/1250000000000000000000 : ℝ)*base91 + (9588591/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (486701139897130367835127203/215078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33391151/100000000000000 : ℝ)*(base1) + (263755467/50000000000000 : ℝ)*(base19) + (279488631/50000000000000 : ℝ)*(base23) + (8138321/20000000000000 : ℝ)*(upper3) + (46842841/100000000000000 : ℝ)*(upper5) + (68392503565259/6250000000000 : ℝ)*(major0) + (68392503565259/6250000000000 : ℝ)*(major1) + (68392503565259/6250000000000 : ℝ)*(major2) + (944643679/50000000000000 : ℝ)*(sp1) + (2478180167/100000000000000 : ℝ)*(sp2) + (363734925653559/25000000000000 : ℝ)*(sp4) + (727468626212397/50000000000000 : ℝ)*(sp5) + (1454936632065657/100000000000000 : ℝ)*(sp6) + (146724067208783/20000000000000 : ℝ)*(sp7) + (366810184717533/50000000000000 : ℝ)*(f.failure) + (290987933844617/20000000000000 : ℝ)*(f.sum) + (153618151140907/68825000000000000000000000000 : ℝ)*base66 + (976097401795140181/107539062500000000000000000000000 : ℝ)*base67 + (50203186505890403/53769531250000000000000000000000 : ℝ)*base69 + (437541846050296431/107539062500000000000000000000000 : ℝ)*base71 + (66993894647443/68825000000000000000000000000 : ℝ)*base73 + (756332803748922319/107539062500000000000000000000000 : ℝ)*base76 + (48779607413922319/107539062500000000000000000000000 : ℝ)*base78 + (312397171896764737/215078125000000000000000000000000 : ℝ)*base79 + (38037577366179/8603125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (444199/625000000000000000000 : ℝ)*base89 + (444199/625000000000000000000 : ℝ)*base91 + (444199/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1126_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2051/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1126_s2_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-539200951/2500000000 : ℝ)*x 0 + (1102776549/2000000000 : ℝ)*x 1 + (1289110357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539200951/2500000000 : ℝ)^8319 ≤ (13069071472981/100000000000000 : ℝ)^6271 := by
    have hnat : (539200951 : ℕ)^8319*100000000000000^6271 ≤ 13069071472981^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539200951 2500000000 13069071472981 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102776549/2000000000 : ℝ)^8319 ≤ (11349116146869/25000000000000 : ℝ)^6271 := by
    have hnat : (1102776549 : ℕ)^8319*25000000000000^6271 ≤ 11349116146869^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102776549 2000000000 11349116146869 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289110357/2500000000 : ℝ)^8319 ≤ (41534463923141/100000000000000 : ℝ)^6271 := by
    have hnat : (1289110357 : ℕ)^8319*100000000000000^6271 ≤ 41534463923141^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289110357 2500000000 41534463923141 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539200951/2500000000 : ℝ), (1102776549/2000000000 : ℝ), (1289110357/2500000000 : ℝ)] ![(13069071472981/100000000000000 : ℝ), (11349116146869/25000000000000 : ℝ), (41534463923141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539200951/2500000000 : ℝ)|^8319 ≤ (13069071472981/100000000000000 : ℝ)^6271
        have hw : |(-539200951/2500000000 : ℝ)|=(539200951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102776549/2000000000 : ℝ)|^8319 ≤ (11349116146869/25000000000000 : ℝ)^6271
        have hw : |(1102776549/2000000000 : ℝ)|=(1102776549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1289110357/2500000000 : ℝ)|^8319 ≤ (41534463923141/100000000000000 : ℝ)^6271
        have hw : |(1289110357/2500000000 : ℝ)|=(1289110357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s2_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374554717/10000000000 : ℝ)*x 0 + (-2342755077/10000000000 : ℝ)*x 1 + (2578221519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374554717/10000000000 : ℝ)^8319 ≤ (137128282641/312500000000 : ℝ)^6271 := by
    have hnat : (5374554717 : ℕ)^8319*312500000000^6271 ≤ 137128282641^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374554717 10000000000 137128282641 312500000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2342755077/10000000000 : ℝ)^8319 ≤ (14584468412287/100000000000000 : ℝ)^6271 := by
    have hnat : (2342755077 : ℕ)^8319*100000000000000^6271 ≤ 14584468412287^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342755077 10000000000 14584468412287 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578221519/5000000000 : ℝ)^8319 ≤ (41534481126717/100000000000000 : ℝ)^6271 := by
    have hnat : (2578221519 : ℕ)^8319*100000000000000^6271 ≤ 41534481126717^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578221519 5000000000 41534481126717 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374554717/10000000000 : ℝ), (-2342755077/10000000000 : ℝ), (2578221519/5000000000 : ℝ)] ![(137128282641/312500000000 : ℝ), (14584468412287/100000000000000 : ℝ), (41534481126717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374554717/10000000000 : ℝ)|^8319 ≤ (137128282641/312500000000 : ℝ)^6271
        have hw : |(5374554717/10000000000 : ℝ)|=(5374554717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2342755077/10000000000 : ℝ)|^8319 ≤ (14584468412287/100000000000000 : ℝ)^6271
        have hw : |(-2342755077/10000000000 : ℝ)|=(2342755077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578221519/5000000000 : ℝ)|^8319 ≤ (41534481126717/100000000000000 : ℝ)^6271
        have hw : |(2578221519/5000000000 : ℝ)|=(2578221519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s2_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687277319/5000000000 : ℝ)*x 0 + (5156443073/10000000000 : ℝ)*x 1 + (-468551027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687277319/5000000000 : ℝ)^8319 ≤ (4388104958947/10000000000000 : ℝ)^6271 := by
    have hnat : (2687277319 : ℕ)^8319*10000000000000^6271 ≤ 4388104958947^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687277319 5000000000 4388104958947 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5156443073/10000000000 : ℝ)^8319 ≤ (10383620375177/25000000000000 : ℝ)^6271 := by
    have hnat : (5156443073 : ℕ)^8319*25000000000000^6271 ≤ 10383620375177^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156443073 10000000000 10383620375177 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468551027/2000000000 : ℝ)^8319 ≤ (3646117222819/25000000000000 : ℝ)^6271 := by
    have hnat : (468551027 : ℕ)^8319*25000000000000^6271 ≤ 3646117222819^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468551027 2000000000 3646117222819 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687277319/5000000000 : ℝ), (5156443073/10000000000 : ℝ), (-468551027/2000000000 : ℝ)] ![(4388104958947/10000000000000 : ℝ), (10383620375177/25000000000000 : ℝ), (3646117222819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687277319/5000000000 : ℝ)|^8319 ≤ (4388104958947/10000000000000 : ℝ)^6271
        have hw : |(2687277319/5000000000 : ℝ)|=(2687277319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5156443073/10000000000 : ℝ)|^8319 ≤ (10383620375177/25000000000000 : ℝ)^6271
        have hw : |(5156443073/10000000000 : ℝ)|=(5156443073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468551027/2000000000 : ℝ)|^8319 ≤ (3646117222819/25000000000000 : ℝ)^6271
        have hw : |(-468551027/2000000000 : ℝ)|=(468551027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s2_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174234463/400000000 : ℝ)*x 0 + (1003940673/2500000000 : ℝ)*x 1 + (188985919/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174234463/400000000 : ℝ)^8319 ≤ (1328195189121/4000000000000 : ℝ)^6271 := by
    have hnat : (174234463 : ℕ)^8319*4000000000000^6271 ≤ 1328195189121^6271*400000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174234463 400000000 1328195189121 4000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003940673/2500000000 : ℝ)^8319 ≤ (931570154583/3125000000000 : ℝ)^6271 := by
    have hnat : (1003940673 : ℕ)^8319*3125000000000^6271 ≤ 931570154583^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003940673 2500000000 931570154583 3125000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188985919/400000000 : ℝ)^8319 ≤ (36984875316347/100000000000000 : ℝ)^6271 := by
    have hnat : (188985919 : ℕ)^8319*100000000000000^6271 ≤ 36984875316347^6271*400000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188985919 400000000 36984875316347 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174234463/400000000 : ℝ), (1003940673/2500000000 : ℝ), (188985919/400000000 : ℝ)] ![(1328195189121/4000000000000 : ℝ), (931570154583/3125000000000 : ℝ), (36984875316347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174234463/400000000 : ℝ)|^8319 ≤ (1328195189121/4000000000000 : ℝ)^6271
        have hw : |(174234463/400000000 : ℝ)|=(174234463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003940673/2500000000 : ℝ)|^8319 ≤ (931570154583/3125000000000 : ℝ)^6271
        have hw : |(1003940673/2500000000 : ℝ)|=(1003940673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188985919/400000000 : ℝ)|^8319 ≤ (36984875316347/100000000000000 : ℝ)^6271
        have hw : |(188985919/400000000 : ℝ)|=(188985919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s2_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078455479/5000000000 : ℝ)*x 0 + (5158934159/10000000000 : ℝ)*x 1 + (5511364739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078455479/5000000000 : ℝ)^8319 ≤ (13069932824307/100000000000000 : ℝ)^6271 := by
    have hnat : (1078455479 : ℕ)^8319*100000000000000^6271 ≤ 13069932824307^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078455479 5000000000 13069932824307 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158934159/10000000000 : ℝ)^8319 ≤ (10390275494917/25000000000000 : ℝ)^6271 := by
    have hnat : (5158934159 : ℕ)^8319*25000000000000^6271 ≤ 10390275494917^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158934159 10000000000 10390275494917 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511364739/10000000000 : ℝ)^8319 ≤ (45368965188633/100000000000000 : ℝ)^6271 := by
    have hnat : (5511364739 : ℕ)^8319*100000000000000^6271 ≤ 45368965188633^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511364739 10000000000 45368965188633 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078455479/5000000000 : ℝ), (5158934159/10000000000 : ℝ), (5511364739/10000000000 : ℝ)] ![(13069932824307/100000000000000 : ℝ), (10390275494917/25000000000000 : ℝ), (45368965188633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078455479/5000000000 : ℝ)|^8319 ≤ (13069932824307/100000000000000 : ℝ)^6271
        have hw : |(-1078455479/5000000000 : ℝ)|=(1078455479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158934159/10000000000 : ℝ)|^8319 ≤ (10390275494917/25000000000000 : ℝ)^6271
        have hw : |(5158934159/10000000000 : ℝ)|=(5158934159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511364739/10000000000 : ℝ)|^8319 ≤ (45368965188633/100000000000000 : ℝ)^6271
        have hw : |(5511364739/10000000000 : ℝ)|=(5511364739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s2_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528395977/1000000000 : ℝ)*x 0 + (-1987831683/10000000000 : ℝ)*x 1 + (1102273057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528395977/1000000000 : ℝ)^8319 ≤ (4290252703247/10000000000000 : ℝ)^6271 := by
    have hnat : (528395977 : ℕ)^8319*10000000000000^6271 ≤ 4290252703247^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528395977 1000000000 4290252703247 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987831683/10000000000 : ℝ)^8319 ≤ (91628920329/781250000000 : ℝ)^6271 := by
    have hnat : (1987831683 : ℕ)^8319*781250000000^6271 ≤ 91628920329^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987831683 10000000000 91628920329 781250000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102273057/2000000000 : ℝ)^8319 ≤ (4536897115111/10000000000000 : ℝ)^6271 := by
    have hnat : (1102273057 : ℕ)^8319*10000000000000^6271 ≤ 4536897115111^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102273057 2000000000 4536897115111 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528395977/1000000000 : ℝ), (-1987831683/10000000000 : ℝ), (1102273057/2000000000 : ℝ)] ![(4290252703247/10000000000000 : ℝ), (91628920329/781250000000 : ℝ), (4536897115111/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528395977/1000000000 : ℝ)|^8319 ≤ (4290252703247/10000000000000 : ℝ)^6271
        have hw : |(528395977/1000000000 : ℝ)|=(528395977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987831683/10000000000 : ℝ)|^8319 ≤ (91628920329/781250000000 : ℝ)^6271
        have hw : |(-1987831683/10000000000 : ℝ)|=(1987831683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102273057/2000000000 : ℝ)|^8319 ≤ (4536897115111/10000000000000 : ℝ)^6271
        have hw : |(1102273057/2000000000 : ℝ)|=(1102273057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s2_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641979273/5000000000 : ℝ)*x 0 + (2755682581/5000000000 : ℝ)*x 1 + (-99391677/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641979273/5000000000 : ℝ)^8319 ≤ (10725628462179/25000000000000 : ℝ)^6271 := by
    have hnat : (2641979273 : ℕ)^8319*25000000000000^6271 ≤ 10725628462179^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641979273 5000000000 10725628462179 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755682581/5000000000 : ℝ)^8319 ≤ (22684484903957/50000000000000 : ℝ)^6271 := by
    have hnat : (2755682581 : ℕ)^8319*50000000000000^6271 ≤ 22684484903957^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755682581 5000000000 22684484903957 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99391677/500000000 : ℝ)^8319 ≤ (11728516336917/100000000000000 : ℝ)^6271 := by
    have hnat : (99391677 : ℕ)^8319*100000000000000^6271 ≤ 11728516336917^6271*500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99391677 500000000 11728516336917 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641979273/5000000000 : ℝ), (2755682581/5000000000 : ℝ), (-99391677/500000000 : ℝ)] ![(10725628462179/25000000000000 : ℝ), (22684484903957/50000000000000 : ℝ), (11728516336917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641979273/5000000000 : ℝ)|^8319 ≤ (10725628462179/25000000000000 : ℝ)^6271
        have hw : |(2641979273/5000000000 : ℝ)|=(2641979273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755682581/5000000000 : ℝ)|^8319 ≤ (22684484903957/50000000000000 : ℝ)^6271
        have hw : |(2755682581/5000000000 : ℝ)|=(2755682581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99391677/500000000 : ℝ)|^8319 ≤ (11728516336917/100000000000000 : ℝ)^6271
        have hw : |(-99391677/500000000 : ℝ)|=(99391677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s2_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178036813/5000000000 : ℝ)*x 0 + (4719705577/10000000000 : ℝ)*x 1 + (4020754917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178036813/5000000000 : ℝ)^8319 ≤ (6641404825747/20000000000000 : ℝ)^6271 := by
    have hnat : (2178036813 : ℕ)^8319*20000000000000^6271 ≤ 6641404825747^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178036813 5000000000 6641404825747 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4719705577/10000000000 : ℝ)^8319 ≤ (36933559347427/100000000000000 : ℝ)^6271 := by
    have hnat : (4719705577 : ℕ)^8319*100000000000000^6271 ≤ 36933559347427^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719705577 10000000000 36933559347427 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020754917/10000000000 : ℝ)^8319 ≤ (3732427065007/12500000000000 : ℝ)^6271 := by
    have hnat : (4020754917 : ℕ)^8319*12500000000000^6271 ≤ 3732427065007^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020754917 10000000000 3732427065007 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178036813/5000000000 : ℝ), (4719705577/10000000000 : ℝ), (4020754917/10000000000 : ℝ)] ![(6641404825747/20000000000000 : ℝ), (36933559347427/100000000000000 : ℝ), (3732427065007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178036813/5000000000 : ℝ)|^8319 ≤ (6641404825747/20000000000000 : ℝ)^6271
        have hw : |(2178036813/5000000000 : ℝ)|=(2178036813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4719705577/10000000000 : ℝ)|^8319 ≤ (36933559347427/100000000000000 : ℝ)^6271
        have hw : |(4719705577/10000000000 : ℝ)|=(4719705577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020754917/10000000000 : ℝ)|^8319 ≤ (3732427065007/12500000000000 : ℝ)^6271
        have hw : |(4020754917/10000000000 : ℝ)|=(4020754917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2051/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8997/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16551/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2051/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2051/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2051/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2051/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2051/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2051/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5559/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (399709602556409/50000000000000000000 : ℝ) := by
    have hpowers : (5559/100000 : ℝ)^4159 ≤ (399709602556409/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5559 : ℕ)^4159*50000000000000000000^1024 ≤ 399709602556409^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5559 100000 399709602556409 50000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5559/100000 : ℝ)) (X := (399709602556409/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2051/10000 : ℝ) ^ (4159/1024 : ℝ) ≤ (32104240449054049/20000000000000000000 : ℝ) := by
    have hpowers : (2051/10000 : ℝ)^4159 ≤ (32104240449054049/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2051 : ℕ)^4159*20000000000000000000^1024 ≤ 32104240449054049^1024*10000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2051 10000 32104240449054049 20000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2051/10000 : ℝ)) (X := (32104240449054049/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000399709602556409/25000000000000000000 : ℝ) ≤ (2500009841312013/2500000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (25000399709602556409/25000000000000000000 : ℝ)^1024 ≤ (2500009841312013/2500000000000000 : ℝ)^4159 := by
      have hnat : (25000399709602556409 : ℕ)^1024*2500000000000000^4159 ≤ 2500009841312013^4159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000399709602556409 25000000000000000000 2500009841312013 2500000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009841312013/2500000000000000 : ℝ)) (X := (25000399709602556409/25000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100161320621450383063/100000000000000000000 : ℝ) ≤ (10003969511250557/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (100161320621450383063/100000000000000000000 : ℝ)^1024 ≤ (10003969511250557/10000000000000000 : ℝ)^4159 := by
      have hnat : (100161320621450383063 : ℕ)^1024*10000000000000000^4159 ≤ 10003969511250557^4159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100161320621450383063 100000000000000000000 10003969511250557 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003969511250557/10000000000000000 : ℝ)) (X := (100161320621450383063/100000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10032104240449054049/10000000000000000000 : ℝ) ≤ (5003949828626531/5000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (10032104240449054049/10000000000000000000 : ℝ)^1024 ≤ (5003949828626531/5000000000000000 : ℝ)^4159 := by
      have hnat : (10032104240449054049 : ℕ)^1024*5000000000000000^4159 ≤ 5003949828626531^4159*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10032104240449054049 10000000000000000000 5003949828626531 5000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003949828626531/5000000000000000 : ℝ)) (X := (10032104240449054049/10000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(399709602556409/50000000000000000000 : ℝ) ≤ ((74733446593283887431/74755000000000000000 : ℝ)+2*(786029200501/299020000000000 : ℝ)*(5559/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (74733446593283887431/74755000000000000000 : ℝ)+2*(786029200501/299020000000000 : ℝ)*(5559/100000 : ℝ)=(2500009841312013/2500000000000000 : ℝ) by norm_num, show 1+2*(399709602556409/50000000000000000000 : ℝ)=(25000399709602556409/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32104240449054049/20000000000000000000 : ℝ)+(399709602556409/50000000000000000000 : ℝ) ≤ ((74733446593283887431/74755000000000000000 : ℝ)+(786029200501/299020000000000 : ℝ)*((2051/10000 : ℝ)+(5559/100000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (74733446593283887431/74755000000000000000 : ℝ)+(786029200501/299020000000000 : ℝ)*((2051/10000 : ℝ)+(5559/100000 : ℝ))=(10003969511250557/10000000000000000 : ℝ) by norm_num, show 1+(32104240449054049/20000000000000000000 : ℝ)+(399709602556409/50000000000000000000 : ℝ)=(100161320621450383063/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32104240449054049/20000000000000000000 : ℝ) ≤ ((74733446593283887431/74755000000000000000 : ℝ)+2*(786029200501/299020000000000 : ℝ)*(2051/10000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (74733446593283887431/74755000000000000000 : ℝ)+2*(786029200501/299020000000000 : ℝ)*(2051/10000 : ℝ)=(5003949828626531/5000000000000000 : ℝ) by norm_num, show 1+2*(32104240449054049/20000000000000000000 : ℝ)=(10032104240449054049/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74733446593283887431/74755000000000000000 : ℝ)*(X 1 0+X 2 0)+(786029200501/299020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (5559/100000 : ℝ)) (hi := (2051/10000 : ℝ)) (c := (74733446593283887431/74755000000000000000 : ℝ)) (alpha := (786029200501/299020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74733446593283887431/74755000000000000000 : ℝ)*(X 0 1+X 2 1)+(786029200501/299020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (5559/100000 : ℝ)) (hi := (2051/10000 : ℝ)) (c := (74733446593283887431/74755000000000000000 : ℝ)) (alpha := (786029200501/299020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74733446593283887431/74755000000000000000 : ℝ)*(X 0 2+X 1 2)+(786029200501/299020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (5559/100000 : ℝ)) (hi := (2051/10000 : ℝ)) (c := (74733446593283887431/74755000000000000000 : ℝ)) (alpha := (786029200501/299020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-539200951/2500000000 : ℝ)*X 0 0+(1102776549/2000000000 : ℝ)*X 0 1+(1289110357/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374554717/10000000000 : ℝ)*X 1 0+(-2342755077/10000000000 : ℝ)*X 1 1+(2578221519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687277319/5000000000 : ℝ)*X 2 0+(5156443073/10000000000 : ℝ)*X 2 1+(-468551027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174234463/400000000 : ℝ)*X 0 0+(1003940673/2500000000 : ℝ)*X 0 1+(188985919/400000000 : ℝ)*X 0 2+(174234463/400000000 : ℝ)*X 1 0+(1003940673/2500000000 : ℝ)*X 1 1+(188985919/400000000 : ℝ)*X 1 2+(174234463/400000000 : ℝ)*X 2 0+(1003940673/2500000000 : ℝ)*X 2 1+(188985919/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1078455479/5000000000 : ℝ)*X 0 0+(5158934159/10000000000 : ℝ)*X 0 1+(5511364739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528395977/1000000000 : ℝ)*X 1 0+(-1987831683/10000000000 : ℝ)*X 1 1+(1102273057/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641979273/5000000000 : ℝ)*X 2 0+(2755682581/5000000000 : ℝ)*X 2 1+(-99391677/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178036813/5000000000 : ℝ)*X 0 0+(4719705577/10000000000 : ℝ)*X 0 1+(4020754917/10000000000 : ℝ)*X 0 2+(2178036813/5000000000 : ℝ)*X 1 0+(4719705577/10000000000 : ℝ)*X 1 1+(4020754917/10000000000 : ℝ)*X 1 2+(2178036813/5000000000 : ℝ)*X 2 0+(4719705577/10000000000 : ℝ)*X 2 1+(4020754917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8102820839408408793400957419/934437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231760939/25000000000000 : ℝ)*(base19) + (23821089/4000000000000 : ℝ)*(base23) + (136376127/50000000000000 : ℝ)*(upper3) + (31214709/20000000000000 : ℝ)*(upper4) + (5219043/100000000000000 : ℝ)*(upper5) + (1052094438650217/50000000000000 : ℝ)*(major0) + (1052094438650217/50000000000000 : ℝ)*(major1) + (1052094438650217/50000000000000 : ℝ)*(major2) + (55953654092089/2000000000000 : ℝ)*(sp0) + (1398849717397803/50000000000000 : ℝ)*(sp1) + (2797699766312137/100000000000000 : ℝ)*(sp2) + (44083438089881/3125000000000 : ℝ)*(sp3) + (551788591/3125000000000 : ℝ)*(sp4) + (7084840803/100000000000000 : ℝ)*(sp7) + (282135420743399/20000000000000 : ℝ)*(f.failure) + (1398850180919681/50000000000000 : ℝ)*(f.sum) + (10784165379/29201171875000000000000000 : ℝ)*base66 + (14641008271940222527/3737750000000000000000000000000000 : ℝ)*base67 + (18070578295098722527/3737750000000000000000000000000000 : ℝ)*base69 + (17264923248245972527/3737750000000000000000000000000000 : ℝ)*base71 + (24050340996449/14951000000000000000000000000 : ℝ)*base74 + (7074235683733722527/3737750000000000000000000000000000 : ℝ)*base75 + (2647076740069972527/3737750000000000000000000000000000 : ℝ)*base77 + (14065295755708027473/3737750000000000000000000000000000 : ℝ)*base80 + (11146483432089/7475500000000000000000000000 : ℝ)*base81 + (264997/250000000000000000000 : ℝ)*base89 + (264997/250000000000000000000 : ℝ)*base91 + (264997/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2262991673537057084738234457/233609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (176939243/10000000000000 : ℝ)*(base19) + (79287301/6250000000000 : ℝ)*(base23) + (5442121/2500000000000 : ℝ)*(upper2) + (23125591/20000000000000 : ℝ)*(upper3) + (17212131/6250000000000 : ℝ)*(upper5) + (266759244789749/12500000000000 : ℝ)*(major0) + (266759244789749/12500000000000 : ℝ)*(major1) + (266759244789749/12500000000000 : ℝ)*(major2) + (23484344469/100000000000000 : ℝ)*(sp1) + (343303859/4000000000000 : ℝ)*(sp2) + (1418717560762061/50000000000000 : ℝ)*(sp4) + (354676233473403/12500000000000 : ℝ)*(sp5) + (177339079395677/6250000000000 : ℝ)*(sp6) + (286142494441867/20000000000000 : ℝ)*(sp7) + (286142494441867/20000000000000 : ℝ)*(f.failure) + (1418717560762061/50000000000000 : ℝ)*(f.sum) + (32342368337071/7475500000000000000000000000 : ℝ)*base66 + (7261685859725807319/934437500000000000000000000000000 : ℝ)*base67 + (4038503887565442681/934437500000000000000000000000000 : ℝ)*base70 + (3674076168666067681/934437500000000000000000000000000 : ℝ)*base72 + (9272586274651/7475500000000000000000000000 : ℝ)*base73 + (12785064557959442681/934437500000000000000000000000000 : ℝ)*base76 + (2491641356736005181/934437500000000000000000000000000 : ℝ)*base78 + (4361743947837380181/934437500000000000000000000000000 : ℝ)*base80 + (29563919021149/7475500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1914001/250000000000000000000 : ℝ)*base89 + (1914001/250000000000000000000 : ℝ)*base91 + (1914001/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1126_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2051/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16551/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1126_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16551/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1126_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1126_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1126_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16551/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
