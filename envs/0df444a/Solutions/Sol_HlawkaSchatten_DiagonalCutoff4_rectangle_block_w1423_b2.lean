-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1423_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:12.037049+00:00
-- url     : https://prove2.me/submissions/3dba9950-0fd3-4266-b0e8-357db1e1b706

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
theorem support_rectangle_w1423_s6_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-988003553/5000000000 : ℝ)*x 0 + (5408532377/10000000000 : ℝ)*x 1 + (524676813/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988003553/5000000000 : ℝ)^4383 ≤ (2410670021587/20000000000000 : ℝ)^3359 := by
    have hnat : (988003553 : ℕ)^4383*20000000000000^3359 ≤ 2410670021587^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988003553 5000000000 2410670021587 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408532377/10000000000 : ℝ)^4383 ≤ (1793775084347/4000000000000 : ℝ)^3359 := by
    have hnat : (5408532377 : ℕ)^4383*4000000000000^3359 ≤ 1793775084347^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408532377 10000000000 1793775084347 4000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524676813/1000000000 : ℝ)^4383 ≤ (10775568193417/25000000000000 : ℝ)^3359 := by
    have hnat : (524676813 : ℕ)^4383*25000000000000^3359 ≤ 10775568193417^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524676813 1000000000 10775568193417 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-988003553/5000000000 : ℝ), (5408532377/10000000000 : ℝ), (524676813/1000000000 : ℝ)] ![(2410670021587/20000000000000 : ℝ), (1793775084347/4000000000000 : ℝ), (10775568193417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-988003553/5000000000 : ℝ)|^4383 ≤ (2410670021587/20000000000000 : ℝ)^3359
        have hw : |(-988003553/5000000000 : ℝ)|=(988003553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408532377/10000000000 : ℝ)|^4383 ≤ (1793775084347/4000000000000 : ℝ)^3359
        have hw : |(5408532377/10000000000 : ℝ)|=(5408532377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524676813/1000000000 : ℝ)|^4383 ≤ (10775568193417/25000000000000 : ℝ)^3359
        have hw : |(524676813/1000000000 : ℝ)|=(524676813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s6_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069490779/2000000000 : ℝ)*x 0 + (-1029184221/5000000000 : ℝ)*x 1 + (81980751/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069490779/2000000000 : ℝ)^4383 ≤ (44184705066313/100000000000000 : ℝ)^3359 := by
    have hnat : (1069490779 : ℕ)^4383*100000000000000^3359 ≤ 44184705066313^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069490779 2000000000 44184705066313 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029184221/5000000000 : ℝ)^4383 ≤ (12713022854463/100000000000000 : ℝ)^3359 := by
    have hnat : (1029184221 : ℕ)^4383*100000000000000^3359 ≤ 12713022854463^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029184221 5000000000 12713022854463 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81980751/156250000 : ℝ)^4383 ≤ (43102272066189/100000000000000 : ℝ)^3359 := by
    have hnat : (81980751 : ℕ)^4383*100000000000000^3359 ≤ 43102272066189^3359*156250000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81980751 156250000 43102272066189 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069490779/2000000000 : ℝ), (-1029184221/5000000000 : ℝ), (81980751/156250000 : ℝ)] ![(44184705066313/100000000000000 : ℝ), (12713022854463/100000000000000 : ℝ), (43102272066189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069490779/2000000000 : ℝ)|^4383 ≤ (44184705066313/100000000000000 : ℝ)^3359
        have hw : |(1069490779/2000000000 : ℝ)|=(1069490779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029184221/5000000000 : ℝ)|^4383 ≤ (12713022854463/100000000000000 : ℝ)^3359
        have hw : |(-1029184221/5000000000 : ℝ)|=(1029184221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81980751/156250000 : ℝ)|^4383 ≤ (43102272066189/100000000000000 : ℝ)^3359
        have hw : |(81980751/156250000 : ℝ)|=(81980751/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s6_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069490847/2000000000 : ℝ)*x 0 + (5246767781/10000000000 : ℝ)*x 1 + (-514592091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069490847/2000000000 : ℝ)^4383 ≤ (11046177183021/25000000000000 : ℝ)^3359 := by
    have hnat : (1069490847 : ℕ)^4383*25000000000000^3359 ≤ 11046177183021^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069490847 2000000000 11046177183021 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246767781/10000000000 : ℝ)^4383 ≤ (10775567258151/25000000000000 : ℝ)^3359 := by
    have hnat : (5246767781 : ℕ)^4383*25000000000000^3359 ≤ 10775567258151^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246767781 10000000000 10775567258151 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514592091/2500000000 : ℝ)^4383 ≤ (3178255556463/25000000000000 : ℝ)^3359 := by
    have hnat : (514592091 : ℕ)^4383*25000000000000^3359 ≤ 3178255556463^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514592091 2500000000 3178255556463 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069490847/2000000000 : ℝ), (5246767781/10000000000 : ℝ), (-514592091/2500000000 : ℝ)] ![(11046177183021/25000000000000 : ℝ), (10775567258151/25000000000000 : ℝ), (3178255556463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069490847/2000000000 : ℝ)|^4383 ≤ (11046177183021/25000000000000 : ℝ)^3359
        have hw : |(1069490847/2000000000 : ℝ)|=(1069490847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246767781/10000000000 : ℝ)|^4383 ≤ (10775567258151/25000000000000 : ℝ)^3359
        have hw : |(5246767781/10000000000 : ℝ)|=(5246767781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-514592091/2500000000 : ℝ)|^4383 ≤ (3178255556463/25000000000000 : ℝ)^3359
        have hw : |(-514592091/2500000000 : ℝ)|=(514592091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s6_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134558617/312500000 : ℝ)*x 0 + (1033619247/2500000000 : ℝ)*x 1 + (4483658403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134558617/312500000 : ℝ)^4383 ≤ (8326149101433/25000000000000 : ℝ)^3359 := by
    have hnat : (134558617 : ℕ)^4383*25000000000000^3359 ≤ 8326149101433^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134558617 312500000 8326149101433 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033619247/2500000000 : ℝ)^4383 ≤ (6317065465111/20000000000000 : ℝ)^3359 := by
    have hnat : (1033619247 : ℕ)^4383*20000000000000^3359 ≤ 6317065465111^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033619247 2500000000 6317065465111 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483658403/10000000000 : ℝ)^4383 ≤ (7022015250349/20000000000000 : ℝ)^3359 := by
    have hnat : (4483658403 : ℕ)^4383*20000000000000^3359 ≤ 7022015250349^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483658403 10000000000 7022015250349 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134558617/312500000 : ℝ), (1033619247/2500000000 : ℝ), (4483658403/10000000000 : ℝ)] ![(8326149101433/25000000000000 : ℝ), (6317065465111/20000000000000 : ℝ), (7022015250349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134558617/312500000 : ℝ)|^4383 ≤ (8326149101433/25000000000000 : ℝ)^3359
        have hw : |(134558617/312500000 : ℝ)|=(134558617/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033619247/2500000000 : ℝ)|^4383 ≤ (6317065465111/20000000000000 : ℝ)^3359
        have hw : |(1033619247/2500000000 : ℝ)|=(1033619247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483658403/10000000000 : ℝ)|^4383 ≤ (7022015250349/20000000000000 : ℝ)^3359
        have hw : |(4483658403/10000000000 : ℝ)|=(4483658403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s6_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79040743/400000000 : ℝ)*x 0 + (5247351157/10000000000 : ℝ)*x 1 + (1081589253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79040743/400000000 : ℝ)^4383 ≤ (12053441394459/100000000000000 : ℝ)^3359 := by
    have hnat : (79040743 : ℕ)^4383*100000000000000^3359 ≤ 12053441394459^3359*400000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79040743 400000000 12053441394459 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247351157/10000000000 : ℝ)^4383 ≤ (43108522568911/100000000000000 : ℝ)^3359 := by
    have hnat : (5247351157 : ℕ)^4383*100000000000000^3359 ≤ 43108522568911^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247351157 10000000000 43108522568911 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081589253/2000000000 : ℝ)^4383 ≤ (44838036025231/100000000000000 : ℝ)^3359 := by
    have hnat : (1081589253 : ℕ)^4383*100000000000000^3359 ≤ 44838036025231^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081589253 2000000000 44838036025231 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79040743/400000000 : ℝ), (5247351157/10000000000 : ℝ), (1081589253/2000000000 : ℝ)] ![(12053441394459/100000000000000 : ℝ), (43108522568911/100000000000000 : ℝ), (44838036025231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79040743/400000000 : ℝ)|^4383 ≤ (12053441394459/100000000000000 : ℝ)^3359
        have hw : |(-79040743/400000000 : ℝ)|=(79040743/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247351157/10000000000 : ℝ)|^4383 ≤ (43108522568911/100000000000000 : ℝ)^3359
        have hw : |(5247351157/10000000000 : ℝ)|=(5247351157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081589253/2000000000 : ℝ)|^4383 ≤ (44838036025231/100000000000000 : ℝ)^3359
        have hw : |(1081589253/2000000000 : ℝ)|=(1081589253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s6_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41448629/78125000 : ℝ)*x 0 + (-237148743/1250000000 : ℝ)*x 1 + (2703973139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41448629/78125000 : ℝ)^4383 ≤ (10933025411021/25000000000000 : ℝ)^3359 := by
    have hnat : (41448629 : ℕ)^4383*25000000000000^3359 ≤ 10933025411021^3359*78125000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41448629 78125000 10933025411021 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237148743/1250000000 : ℝ)^4383 ≤ (1142986217873/10000000000000 : ℝ)^3359 := by
    have hnat : (237148743 : ℕ)^4383*10000000000000^3359 ≤ 1142986217873^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237148743 1250000000 1142986217873 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703973139/5000000000 : ℝ)^4383 ≤ (358704289327/800000000000 : ℝ)^3359 := by
    have hnat : (2703973139 : ℕ)^4383*800000000000^3359 ≤ 358704289327^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703973139 5000000000 358704289327 800000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41448629/78125000 : ℝ), (-237148743/1250000000 : ℝ), (2703973139/5000000000 : ℝ)] ![(10933025411021/25000000000000 : ℝ), (1142986217873/10000000000000 : ℝ), (358704289327/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41448629/78125000 : ℝ)|^4383 ≤ (10933025411021/25000000000000 : ℝ)^3359
        have hw : |(41448629/78125000 : ℝ)|=(41448629/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237148743/1250000000 : ℝ)|^4383 ≤ (1142986217873/10000000000000 : ℝ)^3359
        have hw : |(-237148743/1250000000 : ℝ)|=(237148743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703973139/5000000000 : ℝ)|^4383 ≤ (358704289327/800000000000 : ℝ)^3359
        have hw : |(2703973139/5000000000 : ℝ)|=(2703973139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s6_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061084943/2000000000 : ℝ)*x 0 + (5407946031/10000000000 : ℝ)*x 1 + (-379438001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061084943/2000000000 : ℝ)^4383 ≤ (21866051913753/50000000000000 : ℝ)^3359 := by
    have hnat : (1061084943 : ℕ)^4383*50000000000000^3359 ≤ 21866051913753^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061084943 2000000000 21866051913753 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407946031/10000000000 : ℝ)^4383 ≤ (11209508373413/25000000000000 : ℝ)^3359 := by
    have hnat : (5407946031 : ℕ)^4383*25000000000000^3359 ≤ 11209508373413^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407946031 10000000000 11209508373413 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379438001/2000000000 : ℝ)^4383 ≤ (5714931329133/50000000000000 : ℝ)^3359 := by
    have hnat : (379438001 : ℕ)^4383*50000000000000^3359 ≤ 5714931329133^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379438001 2000000000 5714931329133 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061084943/2000000000 : ℝ), (5407946031/10000000000 : ℝ), (-379438001/2000000000 : ℝ)] ![(21866051913753/50000000000000 : ℝ), (11209508373413/25000000000000 : ℝ), (5714931329133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061084943/2000000000 : ℝ)|^4383 ≤ (21866051913753/50000000000000 : ℝ)^3359
        have hw : |(1061084943/2000000000 : ℝ)|=(1061084943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407946031/10000000000 : ℝ)|^4383 ≤ (11209508373413/25000000000000 : ℝ)^3359
        have hw : |(5407946031/10000000000 : ℝ)|=(5407946031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379438001/2000000000 : ℝ)|^4383 ≤ (5714931329133/50000000000000 : ℝ)^3359
        have hw : |(-379438001/2000000000 : ℝ)|=(379438001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s6_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152949981/5000000000 : ℝ)*x 0 + (2241199963/5000000000 : ℝ)*x 1 + (165429693/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152949981/5000000000 : ℝ)^4383 ≤ (1665242041457/5000000000000 : ℝ)^3359 := by
    have hnat : (2152949981 : ℕ)^4383*5000000000000^3359 ≤ 1665242041457^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152949981 5000000000 1665242041457 5000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241199963/5000000000 : ℝ)^4383 ≤ (3509721783721/10000000000000 : ℝ)^3359 := by
    have hnat : (2241199963 : ℕ)^4383*10000000000000^3359 ≤ 3509721783721^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241199963 5000000000 3509721783721 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165429693/400000000 : ℝ)^4383 ≤ (31597941322889/100000000000000 : ℝ)^3359 := by
    have hnat : (165429693 : ℕ)^4383*100000000000000^3359 ≤ 31597941322889^3359*400000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165429693 400000000 31597941322889 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152949981/5000000000 : ℝ), (2241199963/5000000000 : ℝ), (165429693/400000000 : ℝ)] ![(1665242041457/5000000000000 : ℝ), (3509721783721/10000000000000 : ℝ), (31597941322889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152949981/5000000000 : ℝ)|^4383 ≤ (1665242041457/5000000000000 : ℝ)^3359
        have hw : |(2152949981/5000000000 : ℝ)|=(2152949981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241199963/5000000000 : ℝ)|^4383 ≤ (3509721783721/10000000000000 : ℝ)^3359
        have hw : |(2241199963/5000000000 : ℝ)|=(2241199963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165429693/400000000 : ℝ)|^4383 ≤ (31597941322889/100000000000000 : ℝ)^3359
        have hw : |(165429693/400000000 : ℝ)|=(165429693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (354/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2831/25000 : ℝ) ^ (2191/512 : ℝ) ≤ (447460356645553/5000000000000000000 : ℝ) := by
    have hpowers : (2831/25000 : ℝ)^2191 ≤ (447460356645553/5000000000000000000 : ℝ)^512 := by
      have hnat : (2831 : ℕ)^2191*5000000000000000000^512 ≤ 447460356645553^512*25000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2831 25000 447460356645553 5000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2831/25000 : ℝ)) (X := (447460356645553/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (2191/512 : ℝ) ≤ (13899270518638091/50000000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^2191 ≤ (13899270518638091/50000000000000000000 : ℝ)^512 := by
      have hnat : (7379 : ℕ)^2191*50000000000000000000^512 ≤ 13899270518638091^512*50000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 13899270518638091 50000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (13899270518638091/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500447460356645553/2500000000000000000 : ℝ) ≤ (10000418227280269/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (2500447460356645553/2500000000000000000 : ℝ)^512 ≤ (10000418227280269/10000000000000000 : ℝ)^2191 := by
      have hnat : (2500447460356645553 : ℕ)^512*10000000000000000^2191 ≤ 10000418227280269^2191*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500447460356645553 2500000000000000000 10000418227280269 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000418227280269/10000000000000000 : ℝ)) (X := (2500447460356645553/2500000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018373874085093621/50000000000000000000 : ℝ) ≤ (5000429306217861/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50018373874085093621/50000000000000000000 : ℝ)^512 ≤ (5000429306217861/5000000000000000 : ℝ)^2191 := by
      have hnat : (50018373874085093621 : ℕ)^512*5000000000000000^2191 ≤ 5000429306217861^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018373874085093621 50000000000000000000 5000429306217861 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000429306217861/5000000000000000 : ℝ)) (X := (50018373874085093621/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013899270518638091/25000000000000000000 : ℝ) ≤ (400051959903647/400000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (25013899270518638091/25000000000000000000 : ℝ)^512 ≤ (400051959903647/400000000000000 : ℝ)^2191 := by
      have hnat : (25013899270518638091 : ℕ)^512*400000000000000^2191 ≤ 400051959903647^2191*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013899270518638091 25000000000000000000 400051959903647 400000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400051959903647/400000000000000 : ℝ)) (X := (25013899270518638091/25000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(447460356645553/5000000000000000000 : ℝ) ≤ ((17165731174739872101/17170000000000000000 : ℝ)+2*(440385155453/343400000000000 : ℝ)*(2831/25000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (17165731174739872101/17170000000000000000 : ℝ)+2*(440385155453/343400000000000 : ℝ)*(2831/25000 : ℝ)=(10000418227280269/10000000000000000 : ℝ) by norm_num, show 1+2*(447460356645553/5000000000000000000 : ℝ)=(2500447460356645553/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13899270518638091/50000000000000000000 : ℝ)+(447460356645553/5000000000000000000 : ℝ) ≤ ((17165731174739872101/17170000000000000000 : ℝ)+(440385155453/343400000000000 : ℝ)*((7379/50000 : ℝ)+(2831/25000 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (17165731174739872101/17170000000000000000 : ℝ)+(440385155453/343400000000000 : ℝ)*((7379/50000 : ℝ)+(2831/25000 : ℝ))=(5000429306217861/5000000000000000 : ℝ) by norm_num, show 1+(13899270518638091/50000000000000000000 : ℝ)+(447460356645553/5000000000000000000 : ℝ)=(50018373874085093621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13899270518638091/50000000000000000000 : ℝ) ≤ ((17165731174739872101/17170000000000000000 : ℝ)+2*(440385155453/343400000000000 : ℝ)*(7379/50000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (17165731174739872101/17170000000000000000 : ℝ)+2*(440385155453/343400000000000 : ℝ)*(7379/50000 : ℝ)=(400051959903647/400000000000000 : ℝ) by norm_num, show 1+2*(13899270518638091/50000000000000000000 : ℝ)=(25013899270518638091/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17165731174739872101/17170000000000000000 : ℝ)*(X 1 0+X 2 0)+(440385155453/343400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (17165731174739872101/17170000000000000000 : ℝ)) (alpha := (440385155453/343400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17165731174739872101/17170000000000000000 : ℝ)*(X 0 1+X 2 1)+(440385155453/343400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (17165731174739872101/17170000000000000000 : ℝ)) (alpha := (440385155453/343400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17165731174739872101/17170000000000000000 : ℝ)*(X 0 2+X 1 2)+(440385155453/343400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (17165731174739872101/17170000000000000000 : ℝ)) (alpha := (440385155453/343400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-988003553/5000000000 : ℝ)*X 0 0+(5408532377/10000000000 : ℝ)*X 0 1+(524676813/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069490779/2000000000 : ℝ)*X 1 0+(-1029184221/5000000000 : ℝ)*X 1 1+(81980751/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069490847/2000000000 : ℝ)*X 2 0+(5246767781/10000000000 : ℝ)*X 2 1+(-514592091/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134558617/312500000 : ℝ)*X 0 0+(1033619247/2500000000 : ℝ)*X 0 1+(4483658403/10000000000 : ℝ)*X 0 2+(134558617/312500000 : ℝ)*X 1 0+(1033619247/2500000000 : ℝ)*X 1 1+(4483658403/10000000000 : ℝ)*X 1 2+(134558617/312500000 : ℝ)*X 2 0+(1033619247/2500000000 : ℝ)*X 2 1+(4483658403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-79040743/400000000 : ℝ)*X 0 0+(5247351157/10000000000 : ℝ)*X 0 1+(1081589253/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41448629/78125000 : ℝ)*X 1 0+(-237148743/1250000000 : ℝ)*X 1 1+(2703973139/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061084943/2000000000 : ℝ)*X 2 0+(5407946031/10000000000 : ℝ)*X 2 1+(-379438001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2152949981/5000000000 : ℝ)*X 0 0+(2241199963/5000000000 : ℝ)*X 0 1+(165429693/400000000 : ℝ)*X 0 2+(2152949981/5000000000 : ℝ)*X 1 0+(2241199963/5000000000 : ℝ)*X 1 1+(165429693/400000000 : ℝ)*X 1 2+(2152949981/5000000000 : ℝ)*X 2 0+(2241199963/5000000000 : ℝ)*X 2 1+(165429693/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28971335195629964834289/8585000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223388133/100000000000000 : ℝ)*(base19) + (315954141/100000000000000 : ℝ)*(base23) + (163661103/100000000000000 : ℝ)*(lower2) + (53353443/100000000000000 : ℝ)*(upper3) + (148903/5000000000000 : ℝ)*(lower4) + (2261418789236953/50000000000000 : ℝ)*(major0) + (2261418789236953/50000000000000 : ℝ)*(major1) + (2261418789236953/50000000000000 : ℝ)*(major2) + (6181831662152229/100000000000000 : ℝ)*(sp0) + (1236366437004127/20000000000000 : ℝ)*(sp1) + (3090916046227313/50000000000000 : ℝ)*(sp2) + (1431920002889441/50000000000000 : ℝ)*(sp3) + (746256539/100000000000000 : ℝ)*(sp4) + (526054391/20000000000000 : ℝ)*(sp7) + (1431921318025419/50000000000000 : ℝ)*(f.failure) + (6181832408408767/100000000000000 : ℝ)*(f.sum) + (13245570231047/4292500000000000000000000000 : ℝ)*base65 + (2742266421671398253/858500000000000000000000000000000 : ℝ)*base67 + (6988876341882601747/858500000000000000000000000000000 : ℝ)*base70 + (9733203157222898253/858500000000000000000000000000000 : ℝ)*base71 + (22061371832249/8585000000000000000000000000 : ℝ)*base73 + (8496798998930101747/858500000000000000000000000000000 : ℝ)*base76 + (4056811761199601747/858500000000000000000000000000000 : ℝ)*base78 + (15180625686096398253/858500000000000000000000000000000 : ℝ)*base79 + (2862459553679/536562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1105537/625000000000000000000 : ℝ)*base89 + (1105537/625000000000000000000 : ℝ)*base91 + (1105537/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2891989538929380834941580927/429250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (271147979/25000000000000 : ℝ)*(base19) + (1404512697/100000000000000 : ℝ)*(base23) + (401765211/100000000000000 : ℝ)*(lower1) + (104380063/100000000000000 : ℝ)*(upper3) + (8605297/25000000000000 : ℝ)*(lower4) + (9557701/25000000000000 : ℝ)*(upper5) + (2277873547828591/50000000000000 : ℝ)*(major0) + (2277873547828591/50000000000000 : ℝ)*(major1) + (2277873547828591/50000000000000 : ℝ)*(major2) + (2119010519/100000000000000 : ℝ)*(sp2) + (6226813156242729/100000000000000 : ℝ)*(sp4) + (6226812071650813/100000000000000 : ℝ)*(sp5) + (6226809632719513/100000000000000 : ℝ)*(sp6) + (144234040524733/5000000000000 : ℝ)*(sp7) + (144234040524733/5000000000000 : ℝ)*(f.failure) + (6226813156242729/100000000000000 : ℝ)*(f.sum) + (11584134812949/4292500000000000000000000000 : ℝ)*base65 + (23830216172186689691/858500000000000000000000000000000 : ℝ)*base67 + (476905058874689691/858500000000000000000000000000000 : ℝ)*base69 + (91305269730851189691/858500000000000000000000000000000 : ℝ)*base71 + (39292110600243/8585000000000000000000000000 : ℝ)*base73 + (150404527313821810309/858500000000000000000000000000000 : ℝ)*base76 + (703723882332810309/858500000000000000000000000000000 : ℝ)*base78 + (23003563269330189691/858500000000000000000000000000000 : ℝ)*base79 + (5856695141701/1073125000000000000000000000 : ℝ)*base81 + (54841/62500000000000000000 : ℝ)*base90 + (54841/62500000000000000000 : ℝ)*base92 + (54841/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1423_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1423_s7_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347446803/10000000000 : ℝ)*x 0 + (-2058341883/10000000000 : ℝ)*x 1 + (1049359033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347446803/10000000000 : ℝ)^4383 ≤ (5523078575333/12500000000000 : ℝ)^3359 := by
    have hnat : (5347446803 : ℕ)^4383*12500000000000^3359 ≤ 5523078575333^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347446803 10000000000 5523078575333 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058341883/10000000000 : ℝ)^4383 ≤ (6356404406467/50000000000000 : ℝ)^3359 := by
    have hnat : (2058341883 : ℕ)^4383*50000000000000^3359 ≤ 6356404406467^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058341883 10000000000 6356404406467 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049359033/2000000000 : ℝ)^4383 ≤ (107756406431/250000000000 : ℝ)^3359 := by
    have hnat : (1049359033 : ℕ)^4383*250000000000^3359 ≤ 107756406431^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049359033 2000000000 107756406431 250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347446803/10000000000 : ℝ), (-2058341883/10000000000 : ℝ), (1049359033/2000000000 : ℝ)] ![(5523078575333/12500000000000 : ℝ), (6356404406467/50000000000000 : ℝ), (107756406431/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347446803/10000000000 : ℝ)|^4383 ≤ (5523078575333/12500000000000 : ℝ)^3359
        have hw : |(5347446803/10000000000 : ℝ)|=(5347446803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058341883/10000000000 : ℝ)|^4383 ≤ (6356404406467/50000000000000 : ℝ)^3359
        have hw : |(-2058341883/10000000000 : ℝ)|=(2058341883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049359033/2000000000 : ℝ)|^4383 ≤ (107756406431/250000000000 : ℝ)^3359
        have hw : |(1049359033/2000000000 : ℝ)|=(1049359033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s7_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-247002689/1250000000 : ℝ)*x 0 + (2623689009/5000000000 : ℝ)*x 1 + (5407917489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247002689/1250000000 : ℝ)^4383 ≤ (6026732385643/50000000000000 : ℝ)^3359 := by
    have hnat : (247002689 : ℕ)^4383*50000000000000^3359 ≤ 6026732385643^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247002689 1250000000 6026732385643 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623689009/5000000000 : ℝ)^4383 ≤ (43108810512221/100000000000000 : ℝ)^3359 := by
    have hnat : (2623689009 : ℕ)^4383*100000000000000^3359 ≤ 43108810512221^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623689009 5000000000 43108810512221 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407917489/10000000000 : ℝ)^4383 ≤ (44837724706141/100000000000000 : ℝ)^3359 := by
    have hnat : (5407917489 : ℕ)^4383*100000000000000^3359 ≤ 44837724706141^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407917489 10000000000 44837724706141 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247002689/1250000000 : ℝ), (2623689009/5000000000 : ℝ), (5407917489/10000000000 : ℝ)] ![(6026732385643/50000000000000 : ℝ), (43108810512221/100000000000000 : ℝ), (44837724706141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247002689/1250000000 : ℝ)|^4383 ≤ (6026732385643/50000000000000 : ℝ)^3359
        have hw : |(-247002689/1250000000 : ℝ)|=(247002689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623689009/5000000000 : ℝ)|^4383 ≤ (43108810512221/100000000000000 : ℝ)^3359
        have hw : |(2623689009/5000000000 : ℝ)|=(2623689009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407917489/10000000000 : ℝ)|^4383 ≤ (44837724706141/100000000000000 : ℝ)^3359
        have hw : |(5407917489/10000000000 : ℝ)|=(5407917489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s7_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305431823/10000000000 : ℝ)*x 0 + (-474304799/2500000000 : ℝ)*x 1 + (2703958877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305431823/10000000000 : ℝ)^4383 ≤ (21866090139783/50000000000000 : ℝ)^3359 := by
    have hnat : (5305431823 : ℕ)^4383*50000000000000^3359 ≤ 21866090139783^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305431823 10000000000 21866090139783 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474304799/2500000000 : ℝ)^4383 ≤ (89297594817/781250000000 : ℝ)^3359 := by
    have hnat : (474304799 : ℕ)^4383*781250000000^3359 ≤ 89297594817^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474304799 2500000000 89297594817 781250000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703958877/5000000000 : ℝ)^4383 ≤ (5604715946637/12500000000000 : ℝ)^3359 := by
    have hnat : (2703958877 : ℕ)^4383*12500000000000^3359 ≤ 5604715946637^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703958877 5000000000 5604715946637 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305431823/10000000000 : ℝ), (-474304799/2500000000 : ℝ), (2703958877/5000000000 : ℝ)] ![(21866090139783/50000000000000 : ℝ), (89297594817/781250000000 : ℝ), (5604715946637/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305431823/10000000000 : ℝ)|^4383 ≤ (21866090139783/50000000000000 : ℝ)^3359
        have hw : |(5305431823/10000000000 : ℝ)|=(5305431823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474304799/2500000000 : ℝ)|^4383 ≤ (89297594817/781250000000 : ℝ)^3359
        have hw : |(-474304799/2500000000 : ℝ)|=(474304799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703958877/5000000000 : ℝ)|^4383 ≤ (5604715946637/12500000000000 : ℝ)^3359
        have hw : |(2703958877/5000000000 : ℝ)|=(2703958877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s7_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305431547/10000000000 : ℝ)*x 0 + (1351979453/2500000000 : ℝ)*x 1 + (-948609747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305431547/10000000000 : ℝ)^4383 ≤ (43732177310971/100000000000000 : ℝ)^3359 := by
    have hnat : (5305431547 : ℕ)^4383*100000000000000^3359 ≤ 43732177310971^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305431547 10000000000 43732177310971 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351979453/2500000000 : ℝ)^4383 ≤ (2241886410029/5000000000000 : ℝ)^3359 := by
    have hnat : (1351979453 : ℕ)^4383*5000000000000^3359 ≤ 2241886410029^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351979453 2500000000 2241886410029 5000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948609747/5000000000 : ℝ)^4383 ≤ (285752361981/2500000000000 : ℝ)^3359 := by
    have hnat : (948609747 : ℕ)^4383*2500000000000^3359 ≤ 285752361981^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948609747 5000000000 285752361981 2500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305431547/10000000000 : ℝ), (1351979453/2500000000 : ℝ), (-948609747/5000000000 : ℝ)] ![(43732177310971/100000000000000 : ℝ), (2241886410029/5000000000000 : ℝ), (285752361981/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305431547/10000000000 : ℝ)|^4383 ≤ (43732177310971/100000000000000 : ℝ)^3359
        have hw : |(5305431547/10000000000 : ℝ)|=(5305431547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351979453/2500000000 : ℝ)|^4383 ≤ (2241886410029/5000000000000 : ℝ)^3359
        have hw : |(1351979453/2500000000 : ℝ)|=(1351979453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948609747/5000000000 : ℝ)|^4383 ≤ (285752361981/2500000000000 : ℝ)^3359
        have hw : |(-948609747/5000000000 : ℝ)|=(948609747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s7_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269118903/625000000 : ℝ)*x 0 + (1120584797/2500000000 : ℝ)*x 1 + (2067901027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269118903/625000000 : ℝ)^4383 ≤ (8326216479863/25000000000000 : ℝ)^3359 := by
    have hnat : (269118903 : ℕ)^4383*25000000000000^3359 ≤ 8326216479863^3359*625000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269118903 625000000 8326216479863 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120584797/2500000000 : ℝ)^4383 ≤ (17548298639057/50000000000000 : ℝ)^3359 := by
    have hnat : (1120584797 : ℕ)^4383*50000000000000^3359 ≤ 17548298639057^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120584797 2500000000 17548298639057 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067901027/5000000000 : ℝ)^4383 ≤ (31598536783423/100000000000000 : ℝ)^3359 := by
    have hnat : (2067901027 : ℕ)^4383*100000000000000^3359 ≤ 31598536783423^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067901027 5000000000 31598536783423 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269118903/625000000 : ℝ), (1120584797/2500000000 : ℝ), (2067901027/5000000000 : ℝ)] ![(8326216479863/25000000000000 : ℝ), (17548298639057/50000000000000 : ℝ), (31598536783423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269118903/625000000 : ℝ)|^4383 ≤ (8326216479863/25000000000000 : ℝ)^3359
        have hw : |(269118903/625000000 : ℝ)|=(269118903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120584797/2500000000 : ℝ)|^4383 ≤ (17548298639057/50000000000000 : ℝ)^3359
        have hw : |(1120584797/2500000000 : ℝ)|=(1120584797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2067901027/5000000000 : ℝ)|^4383 ≤ (31598536783423/100000000000000 : ℝ)^3359
        have hw : |(2067901027/5000000000 : ℝ)|=(2067901027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (354/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (354/3125 : ℝ) ^ (2191/512 : ℝ) ≤ (2240685614064297/25000000000000000000 : ℝ) := by
    have hpowers : (354/3125 : ℝ)^2191 ≤ (2240685614064297/25000000000000000000 : ℝ)^512 := by
      have hnat : (354 : ℕ)^2191*25000000000000000000^512 ≤ 2240685614064297^512*3125^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        354 3125 2240685614064297 25000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (354/3125 : ℝ)) (X := (2240685614064297/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (2191/512 : ℝ) ≤ (27766312997018493/100000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^2191 ≤ (27766312997018493/100000000000000000000 : ℝ)^512 := by
      have hnat : (7377 : ℕ)^2191*100000000000000000000^512 ≤ 27766312997018493^512*50000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 27766312997018493 100000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (27766312997018493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502240685614064297/12500000000000000000 : ℝ) ≤ (31251308936841/31250000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (12502240685614064297/12500000000000000000 : ℝ)^512 ≤ (31251308936841/31250000000000 : ℝ)^2191 := by
      have hnat : (12502240685614064297 : ℕ)^512*31250000000000^2191 ≤ 31251308936841^2191*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502240685614064297 12500000000000000000 31251308936841 31250000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31251308936841/31250000000000 : ℝ)) (X := (12502240685614064297/12500000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036729055453275681/100000000000000000000 : ℝ) ≤ (10000858175741177/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (100036729055453275681/100000000000000000000 : ℝ)^512 ≤ (10000858175741177/10000000000000000 : ℝ)^2191 := by
      have hnat : (100036729055453275681 : ℕ)^512*10000000000000000^2191 ≤ 10000858175741177^2191*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036729055453275681 100000000000000000000 10000858175741177 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000858175741177/10000000000000000 : ℝ)) (X := (100036729055453275681/100000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027766312997018493/50000000000000000000 : ℝ) ≤ (5000648745846617/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50027766312997018493/50000000000000000000 : ℝ)^512 ≤ (5000648745846617/5000000000000000 : ℝ)^2191 := by
      have hnat : (50027766312997018493 : ℕ)^512*5000000000000000^2191 ≤ 5000648745846617^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027766312997018493 50000000000000000000 5000648745846617 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000648745846617/5000000000000000 : ℝ)) (X := (50027766312997018493/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2240685614064297/25000000000000000000 : ℝ) ≤ ((22299141843377423/22304687500000000 : ℝ)+2*(439315952057/342600000000000 : ℝ)*(354/3125 : ℝ))^(2191/512 : ℝ) := by
    rw [show (22299141843377423/22304687500000000 : ℝ)+2*(439315952057/342600000000000 : ℝ)*(354/3125 : ℝ)=(31251308936841/31250000000000 : ℝ) by norm_num, show 1+2*(2240685614064297/25000000000000000000 : ℝ)=(12502240685614064297/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27766312997018493/100000000000000000000 : ℝ)+(2240685614064297/25000000000000000000 : ℝ) ≤ ((22299141843377423/22304687500000000 : ℝ)+(439315952057/342600000000000 : ℝ)*((7377/50000 : ℝ)+(354/3125 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (22299141843377423/22304687500000000 : ℝ)+(439315952057/342600000000000 : ℝ)*((7377/50000 : ℝ)+(354/3125 : ℝ))=(10000858175741177/10000000000000000 : ℝ) by norm_num, show 1+(27766312997018493/100000000000000000000 : ℝ)+(2240685614064297/25000000000000000000 : ℝ)=(100036729055453275681/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27766312997018493/100000000000000000000 : ℝ) ≤ ((22299141843377423/22304687500000000 : ℝ)+2*(439315952057/342600000000000 : ℝ)*(7377/50000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (22299141843377423/22304687500000000 : ℝ)+2*(439315952057/342600000000000 : ℝ)*(7377/50000 : ℝ)=(5000648745846617/5000000000000000 : ℝ) by norm_num, show 1+2*(27766312997018493/100000000000000000000 : ℝ)=(50027766312997018493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22299141843377423/22304687500000000 : ℝ)*(X 1 0+X 2 0)+(439315952057/342600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (22299141843377423/22304687500000000 : ℝ)) (alpha := (439315952057/342600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22299141843377423/22304687500000000 : ℝ)*(X 0 1+X 2 1)+(439315952057/342600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (22299141843377423/22304687500000000 : ℝ)) (alpha := (439315952057/342600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22299141843377423/22304687500000000 : ℝ)*(X 0 2+X 1 2)+(439315952057/342600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (22299141843377423/22304687500000000 : ℝ)) (alpha := (439315952057/342600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5347446803/10000000000 : ℝ)*X 1 0+(-2058341883/10000000000 : ℝ)*X 1 1+(1049359033/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s7_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-247002689/1250000000 : ℝ)*X 0 0+(2623689009/5000000000 : ℝ)*X 0 1+(5407917489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305431823/10000000000 : ℝ)*X 1 0+(-474304799/2500000000 : ℝ)*X 1 1+(2703958877/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305431547/10000000000 : ℝ)*X 2 0+(1351979453/2500000000 : ℝ)*X 2 1+(-948609747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((269118903/625000000 : ℝ)*X 0 0+(1120584797/2500000000 : ℝ)*X 0 1+(2067901027/5000000000 : ℝ)*X 0 2+(269118903/625000000 : ℝ)*X 1 0+(1120584797/2500000000 : ℝ)*X 1 1+(2067901027/5000000000 : ℝ)*X 1 2+(269118903/625000000 : ℝ)*X 2 0+(1120584797/2500000000 : ℝ)*X 2 1+(2067901027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40144405500591280020814227/17843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (838676701/100000000000000 : ℝ)*(base19) + (249333643/50000000000000 : ℝ)*(base23) + (124862307/50000000000000 : ℝ)*(lower1) + (100174283/100000000000000 : ℝ)*(upper3) + (21880101/50000000000000 : ℝ)*(lower4) + (65042503/50000000000000 : ℝ)*(upper5) + (4557331615485881/100000000000000 : ℝ)*(major0) + (4557331615485881/100000000000000 : ℝ)*(major1) + (4557331615485881/100000000000000 : ℝ)*(major2) + (12431297651/100000000000000 : ℝ)*(sp0) + (24331949351081/390625000000 : ℝ)*(sp1) + (389310360243899/6250000000000 : ℝ)*(sp2) + (124579570704189/2000000000000 : ℝ)*(sp3) + (2885684122102553/100000000000000 : ℝ)*(sp4) + (2885684122102553/100000000000000 : ℝ)*(f.failure) + (24331949351081/390625000000 : ℝ)*(f.sum) + (1159210264657/17130000000000000000000000000 : ℝ)*base65 + (457667169312793051/107062500000000000000000000000000 : ℝ)*base68 + (1296300986437081949/107062500000000000000000000000000 : ℝ)*base69 + (35576265060894449/107062500000000000000000000000000 : ℝ)*base71 + (26275546024493/17130000000000000000000000000 : ℝ)*base74 + (1230506043217644449/107062500000000000000000000000000 : ℝ)*base75 + (831907850420581949/107062500000000000000000000000000 : ℝ)*base77 + (399075418038706949/107062500000000000000000000000000 : ℝ)*base79 + (90138928530157/17130000000000000000000000000 : ℝ)*base81 + (4887019/1250000000000000000000 : ℝ)*base89 + (4887019/1250000000000000000000 : ℝ)*base91 + (4887019/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1423_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1423_box_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22686481/125000000 : ℝ)*x 0 + (538651251/1000000000 : ℝ)*x 1 + (5386512001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22686481/125000000 : ℝ)^4383 ≤ (5393712185351/50000000000000 : ℝ)^3359 := by
    have hnat : (22686481 : ℕ)^4383*50000000000000^3359 ≤ 5393712185351^3359*125000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22686481 125000000 5393712185351 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538651251/1000000000 : ℝ)^4383 ≤ (8921258110949/20000000000000 : ℝ)^3359 := by
    have hnat : (538651251 : ℕ)^4383*20000000000000^3359 ≤ 8921258110949^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538651251 1000000000 8921258110949 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386512001/10000000000 : ℝ)^4383 ≤ (22303142527341/50000000000000 : ℝ)^3359 := by
    have hnat : (5386512001 : ℕ)^4383*50000000000000^3359 ≤ 22303142527341^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386512001 10000000000 22303142527341 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22686481/125000000 : ℝ), (538651251/1000000000 : ℝ), (5386512001/10000000000 : ℝ)] ![(5393712185351/50000000000000 : ℝ), (8921258110949/20000000000000 : ℝ), (22303142527341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22686481/125000000 : ℝ)|^4383 ≤ (5393712185351/50000000000000 : ℝ)^3359
        have hw : |(-22686481/125000000 : ℝ)|=(22686481/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538651251/1000000000 : ℝ)|^4383 ≤ (8921258110949/20000000000000 : ℝ)^3359
        have hw : |(538651251/1000000000 : ℝ)|=(538651251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386512001/10000000000 : ℝ)|^4383 ≤ (22303142527341/50000000000000 : ℝ)^3359
        have hw : |(5386512001/10000000000 : ℝ)|=(5386512001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286020587/10000000000 : ℝ)*x 0 + (-1952955479/10000000000 : ℝ)*x 1 + (673314013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286020587/10000000000 : ℝ)^4383 ≤ (43523513855539/100000000000000 : ℝ)^3359 := by
    have hnat : (5286020587 : ℕ)^4383*100000000000000^3359 ≤ 43523513855539^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286020587 10000000000 43523513855539 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952955479/10000000000 : ℝ)^4383 ≤ (59350999783/500000000000 : ℝ)^3359 := by
    have hnat : (1952955479 : ℕ)^4383*500000000000^3359 ≤ 59350999783^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952955479 10000000000 59350999783 500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673314013/1250000000 : ℝ)^4383 ≤ (44606286167661/100000000000000 : ℝ)^3359 := by
    have hnat : (673314013 : ℕ)^4383*100000000000000^3359 ≤ 44606286167661^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673314013 1250000000 44606286167661 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286020587/10000000000 : ℝ), (-1952955479/10000000000 : ℝ), (673314013/1250000000 : ℝ)] ![(43523513855539/100000000000000 : ℝ), (59350999783/500000000000 : ℝ), (44606286167661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286020587/10000000000 : ℝ)|^4383 ≤ (43523513855539/100000000000000 : ℝ)^3359
        have hw : |(5286020587/10000000000 : ℝ)|=(5286020587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952955479/10000000000 : ℝ)|^4383 ≤ (59350999783/500000000000 : ℝ)^3359
        have hw : |(-1952955479/10000000000 : ℝ)|=(1952955479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673314013/1250000000 : ℝ)|^4383 ≤ (44606286167661/100000000000000 : ℝ)^3359
        have hw : |(673314013/1250000000 : ℝ)|=(673314013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321505083/2500000000 : ℝ)*x 0 + (5386512257/10000000000 : ℝ)*x 1 + (-61029863/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321505083/2500000000 : ℝ)^4383 ≤ (21761755557939/50000000000000 : ℝ)^3359 := by
    have hnat : (1321505083 : ℕ)^4383*50000000000000^3359 ≤ 21761755557939^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321505083 2500000000 21761755557939 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386512257/10000000000 : ℝ)^4383 ≤ (22303143910461/50000000000000 : ℝ)^3359 := by
    have hnat : (5386512257 : ℕ)^4383*50000000000000^3359 ≤ 22303143910461^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386512257 10000000000 22303143910461 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61029863/312500000 : ℝ)^4383 ≤ (2374040208629/20000000000000 : ℝ)^3359 := by
    have hnat : (61029863 : ℕ)^4383*20000000000000^3359 ≤ 2374040208629^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61029863 312500000 2374040208629 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321505083/2500000000 : ℝ), (5386512257/10000000000 : ℝ), (-61029863/312500000 : ℝ)] ![(21761755557939/50000000000000 : ℝ), (22303143910461/50000000000000 : ℝ), (2374040208629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321505083/2500000000 : ℝ)|^4383 ≤ (21761755557939/50000000000000 : ℝ)^3359
        have hw : |(1321505083/2500000000 : ℝ)|=(1321505083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386512257/10000000000 : ℝ)|^4383 ≤ (22303143910461/50000000000000 : ℝ)^3359
        have hw : |(5386512257/10000000000 : ℝ)|=(5386512257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61029863/312500000 : ℝ)|^4383 ≤ (2374040208629/20000000000000 : ℝ)^3359
        have hw : |(-61029863/312500000 : ℝ)|=(61029863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4452294331/10000000000 : ℝ)*x 0 + (1059097323/2500000000 : ℝ)*x 1 + (2118194709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452294331/10000000000 : ℝ)^4383 ≤ (34789944245711/100000000000000 : ℝ)^3359 := by
    have hnat : (4452294331 : ℕ)^4383*100000000000000^3359 ≤ 34789944245711^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452294331 10000000000 34789944245711 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059097323/2500000000 : ℝ)^4383 ≤ (16302513616889/50000000000000 : ℝ)^3359 := by
    have hnat : (1059097323 : ℕ)^4383*50000000000000^3359 ≤ 16302513616889^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059097323 2500000000 16302513616889 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118194709/5000000000 : ℝ)^4383 ≤ (16302514249579/50000000000000 : ℝ)^3359 := by
    have hnat : (2118194709 : ℕ)^4383*50000000000000^3359 ≤ 16302514249579^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118194709 5000000000 16302514249579 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452294331/10000000000 : ℝ), (1059097323/2500000000 : ℝ), (2118194709/5000000000 : ℝ)] ![(34789944245711/100000000000000 : ℝ), (16302513616889/50000000000000 : ℝ), (16302514249579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452294331/10000000000 : ℝ)|^4383 ≤ (34789944245711/100000000000000 : ℝ)^3359
        have hw : |(4452294331/10000000000 : ℝ)|=(4452294331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059097323/2500000000 : ℝ)|^4383 ≤ (16302513616889/50000000000000 : ℝ)^3359
        have hw : |(1059097323/2500000000 : ℝ)|=(1059097323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118194709/5000000000 : ℝ)|^4383 ≤ (16302514249579/50000000000000 : ℝ)^3359
        have hw : |(2118194709/5000000000 : ℝ)|=(2118194709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069921067/5000000000 : ℝ)*x 0 + (5266436151/10000000000 : ℝ)*x 1 + (1053287257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069921067/5000000000 : ℝ)^4383 ≤ (6686777100597/50000000000000 : ℝ)^3359 := by
    have hnat : (1069921067 : ℕ)^4383*50000000000000^3359 ≤ 6686777100597^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069921067 5000000000 6686777100597 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266436151/10000000000 : ℝ)^4383 ≤ (43313222172779/100000000000000 : ℝ)^3359 := by
    have hnat : (5266436151 : ℕ)^4383*100000000000000^3359 ≤ 43313222172779^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266436151 10000000000 43313222172779 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053287257/2000000000 : ℝ)^4383 ≤ (8662644722163/20000000000000 : ℝ)^3359 := by
    have hnat : (1053287257 : ℕ)^4383*20000000000000^3359 ≤ 8662644722163^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053287257 2000000000 8662644722163 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069921067/5000000000 : ℝ), (5266436151/10000000000 : ℝ), (1053287257/2000000000 : ℝ)] ![(6686777100597/50000000000000 : ℝ), (43313222172779/100000000000000 : ℝ), (8662644722163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069921067/5000000000 : ℝ)|^4383 ≤ (6686777100597/50000000000000 : ℝ)^3359
        have hw : |(-1069921067/5000000000 : ℝ)|=(1069921067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266436151/10000000000 : ℝ)|^4383 ≤ (43313222172779/100000000000000 : ℝ)^3359
        have hw : |(5266436151/10000000000 : ℝ)|=(5266436151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053287257/2000000000 : ℝ)|^4383 ≤ (8662644722163/20000000000000 : ℝ)^3359
        have hw : |(1053287257/2000000000 : ℝ)|=(1053287257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370076517/10000000000 : ℝ)*x 0 + (-500417353/2500000000 : ℝ)*x 1 + (5266435759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370076517/10000000000 : ℝ)^4383 ≤ (11107193008603/25000000000000 : ℝ)^3359 := by
    have hnat : (5370076517 : ℕ)^4383*25000000000000^3359 ≤ 11107193008603^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370076517 10000000000 11107193008603 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500417353/2500000000 : ℝ)^4383 ≤ (766125623999/6250000000000 : ℝ)^3359 := by
    have hnat : (500417353 : ℕ)^4383*6250000000000^3359 ≤ 766125623999^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500417353 2500000000 766125623999 6250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266435759/10000000000 : ℝ)^4383 ≤ (8662643593197/20000000000000 : ℝ)^3359 := by
    have hnat : (5266435759 : ℕ)^4383*20000000000000^3359 ≤ 8662643593197^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266435759 10000000000 8662643593197 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370076517/10000000000 : ℝ), (-500417353/2500000000 : ℝ), (5266435759/10000000000 : ℝ)] ![(11107193008603/25000000000000 : ℝ), (766125623999/6250000000000 : ℝ), (8662643593197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370076517/10000000000 : ℝ)|^4383 ≤ (11107193008603/25000000000000 : ℝ)^3359
        have hw : |(5370076517/10000000000 : ℝ)|=(5370076517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-500417353/2500000000 : ℝ)|^4383 ≤ (766125623999/6250000000000 : ℝ)^3359
        have hw : |(-500417353/2500000000 : ℝ)|=(500417353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266435759/10000000000 : ℝ)|^4383 ≤ (8662643593197/20000000000000 : ℝ)^3359
        have hw : |(5266435759/10000000000 : ℝ)|=(5266435759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370075901/10000000000 : ℝ)*x 0 + (1316609227/2500000000 : ℝ)*x 1 + (-2001668701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370075901/10000000000 : ℝ)^4383 ≤ (22214382692173/50000000000000 : ℝ)^3359 := by
    have hnat : (5370075901 : ℕ)^4383*50000000000000^3359 ≤ 22214382692173^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370075901 10000000000 22214382692173 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316609227/2500000000 : ℝ)^4383 ≤ (10828307574153/25000000000000 : ℝ)^3359 := by
    have hnat : (1316609227 : ℕ)^4383*25000000000000^3359 ≤ 10828307574153^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316609227 2500000000 10828307574153 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001668701/10000000000 : ℝ)^4383 ≤ (12258004302541/100000000000000 : ℝ)^3359 := by
    have hnat : (2001668701 : ℕ)^4383*100000000000000^3359 ≤ 12258004302541^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001668701 10000000000 12258004302541 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370075901/10000000000 : ℝ), (1316609227/2500000000 : ℝ), (-2001668701/10000000000 : ℝ)] ![(22214382692173/50000000000000 : ℝ), (10828307574153/25000000000000 : ℝ), (12258004302541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370075901/10000000000 : ℝ)|^4383 ≤ (22214382692173/50000000000000 : ℝ)^3359
        have hw : |(5370075901/10000000000 : ℝ)|=(5370075901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316609227/2500000000 : ℝ)|^4383 ≤ (10828307574153/25000000000000 : ℝ)^3359
        have hw : |(1316609227/2500000000 : ℝ)|=(1316609227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2001668701/10000000000 : ℝ)|^4383 ≤ (12258004302541/100000000000000 : ℝ)^3359
        have hw : |(-2001668701/10000000000 : ℝ)|=(2001668701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4158420473/10000000000 : ℝ)*x 0 + (876654981/2000000000 : ℝ)*x 1 + (2191637767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4158420473/10000000000 : ℝ)^4383 ≤ (3182421641459/10000000000000 : ℝ)^3359 := by
    have hnat : (4158420473 : ℕ)^4383*10000000000000^3359 ≤ 3182421641459^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158420473 10000000000 3182421641459 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876654981/2000000000 : ℝ)^4383 ≤ (532623259207/1562500000000 : ℝ)^3359 := by
    have hnat : (876654981 : ℕ)^4383*1562500000000^3359 ≤ 532623259207^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876654981 2000000000 532623259207 1562500000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191637767/5000000000 : ℝ)^4383 ≤ (34087894972081/100000000000000 : ℝ)^3359 := by
    have hnat : (2191637767 : ℕ)^4383*100000000000000^3359 ≤ 34087894972081^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191637767 5000000000 34087894972081 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4158420473/10000000000 : ℝ), (876654981/2000000000 : ℝ), (2191637767/5000000000 : ℝ)] ![(3182421641459/10000000000000 : ℝ), (532623259207/1562500000000 : ℝ), (34087894972081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4158420473/10000000000 : ℝ)|^4383 ≤ (3182421641459/10000000000000 : ℝ)^3359
        have hw : |(4158420473/10000000000 : ℝ)|=(4158420473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876654981/2000000000 : ℝ)|^4383 ≤ (532623259207/1562500000000 : ℝ)^3359
        have hw : |(876654981/2000000000 : ℝ)|=(876654981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2191637767/5000000000 : ℝ)|^4383 ≤ (34087894972081/100000000000000 : ℝ)^3359
        have hw : |(2191637767/5000000000 : ℝ)|=(2191637767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_8 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41428331/200000000 : ℝ)*x 0 + (2591703569/5000000000 : ℝ)*x 1 + (540048981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41428331/200000000 : ℝ)^4383 ≤ (6409140236251/50000000000000 : ℝ)^3359 := by
    have hnat : (41428331 : ℕ)^4383*50000000000000^3359 ≤ 6409140236251^3359*200000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41428331 200000000 6409140236251 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591703569/5000000000 : ℝ)^4383 ≤ (4242433579127/10000000000000 : ℝ)^3359 := by
    have hnat : (2591703569 : ℕ)^4383*10000000000000^3359 ≤ 4242433579127^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591703569 5000000000 4242433579127 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540048981/1000000000 : ℝ)^4383 ≤ (11189345930711/25000000000000 : ℝ)^3359 := by
    have hnat : (540048981 : ℕ)^4383*25000000000000^3359 ≤ 11189345930711^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540048981 1000000000 11189345930711 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41428331/200000000 : ℝ), (2591703569/5000000000 : ℝ), (540048981/1000000000 : ℝ)] ![(6409140236251/50000000000000 : ℝ), (4242433579127/10000000000000 : ℝ), (11189345930711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41428331/200000000 : ℝ)|^4383 ≤ (6409140236251/50000000000000 : ℝ)^3359
        have hw : |(-41428331/200000000 : ℝ)|=(41428331/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591703569/5000000000 : ℝ)|^4383 ≤ (4242433579127/10000000000000 : ℝ)^3359
        have hw : |(2591703569/5000000000 : ℝ)|=(2591703569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540048981/1000000000 : ℝ)|^4383 ≤ (11189345930711/25000000000000 : ℝ)^3359
        have hw : |(540048981/1000000000 : ℝ)|=(540048981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_9 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638115847/5000000000 : ℝ)*x 0 + (-1947158161/10000000000 : ℝ)*x 1 + (5400489807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638115847/5000000000 : ℝ)^4383 ≤ (43418373972289/100000000000000 : ℝ)^3359 := by
    have hnat : (2638115847 : ℕ)^4383*100000000000000^3359 ≤ 43418373972289^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638115847 5000000000 43418373972289 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1947158161/10000000000 : ℝ)^4383 ≤ (11824242329733/100000000000000 : ℝ)^3359 := by
    have hnat : (1947158161 : ℕ)^4383*100000000000000^3359 ≤ 11824242329733^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947158161 10000000000 11824242329733 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400489807/10000000000 : ℝ)^4383 ≤ (44757383690401/100000000000000 : ℝ)^3359 := by
    have hnat : (5400489807 : ℕ)^4383*100000000000000^3359 ≤ 44757383690401^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400489807 10000000000 44757383690401 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638115847/5000000000 : ℝ), (-1947158161/10000000000 : ℝ), (5400489807/10000000000 : ℝ)] ![(43418373972289/100000000000000 : ℝ), (11824242329733/100000000000000 : ℝ), (44757383690401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638115847/5000000000 : ℝ)|^4383 ≤ (43418373972289/100000000000000 : ℝ)^3359
        have hw : |(2638115847/5000000000 : ℝ)|=(2638115847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1947158161/10000000000 : ℝ)|^4383 ≤ (11824242329733/100000000000000 : ℝ)^3359
        have hw : |(-1947158161/10000000000 : ℝ)|=(1947158161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400489807/10000000000 : ℝ)|^4383 ≤ (44757383690401/100000000000000 : ℝ)^3359
        have hw : |(5400489807/10000000000 : ℝ)|=(5400489807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_10 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276231709/10000000000 : ℝ)*x 0 + (5400489747/10000000000 : ℝ)*x 1 + (-1947158221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276231709/10000000000 : ℝ)^4383 ≤ (21709187066677/50000000000000 : ℝ)^3359 := by
    have hnat : (5276231709 : ℕ)^4383*50000000000000^3359 ≤ 21709187066677^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276231709 10000000000 21709187066677 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400489747/10000000000 : ℝ)^4383 ≤ (44757383041551/100000000000000 : ℝ)^3359 := by
    have hnat : (5400489747 : ℕ)^4383*100000000000000^3359 ≤ 44757383041551^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400489747 10000000000 44757383041551 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947158221/10000000000 : ℝ)^4383 ≤ (11824242805161/100000000000000 : ℝ)^3359 := by
    have hnat : (1947158221 : ℕ)^4383*100000000000000^3359 ≤ 11824242805161^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947158221 10000000000 11824242805161 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276231709/10000000000 : ℝ), (5400489747/10000000000 : ℝ), (-1947158221/10000000000 : ℝ)] ![(21709187066677/50000000000000 : ℝ), (44757383041551/100000000000000 : ℝ), (11824242805161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276231709/10000000000 : ℝ)|^4383 ≤ (21709187066677/50000000000000 : ℝ)^3359
        have hw : |(5276231709/10000000000 : ℝ)|=(5276231709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400489747/10000000000 : ℝ)|^4383 ≤ (44757383041551/100000000000000 : ℝ)^3359
        have hw : |(5400489747/10000000000 : ℝ)|=(5400489747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947158221/10000000000 : ℝ)|^4383 ≤ (11824242805161/100000000000000 : ℝ)^3359
        have hw : |(-1947158221/10000000000 : ℝ)|=(1947158221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_11 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4485945789/10000000000 : ℝ)*x 0 + (4219276491/10000000000 : ℝ)*x 1 + (84385531/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4485945789/10000000000 : ℝ)^4383 ≤ (35133450300569/100000000000000 : ℝ)^3359 := by
    have hnat : (4485945789 : ℕ)^4383*100000000000000^3359 ≤ 35133450300569^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485945789 10000000000 35133450300569 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219276491/10000000000 : ℝ)^4383 ≤ (16216637274537/50000000000000 : ℝ)^3359 := by
    have hnat : (4219276491 : ℕ)^4383*50000000000000^3359 ≤ 16216637274537^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219276491 10000000000 16216637274537 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84385531/200000000 : ℝ)^4383 ≤ (32433275140863/100000000000000 : ℝ)^3359 := by
    have hnat : (84385531 : ℕ)^4383*100000000000000^3359 ≤ 32433275140863^3359*200000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84385531 200000000 32433275140863 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4485945789/10000000000 : ℝ), (4219276491/10000000000 : ℝ), (84385531/200000000 : ℝ)] ![(35133450300569/100000000000000 : ℝ), (16216637274537/50000000000000 : ℝ), (32433275140863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4485945789/10000000000 : ℝ)|^4383 ≤ (35133450300569/100000000000000 : ℝ)^3359
        have hw : |(4485945789/10000000000 : ℝ)|=(4485945789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4219276491/10000000000 : ℝ)|^4383 ≤ (16216637274537/50000000000000 : ℝ)^3359
        have hw : |(4219276491/10000000000 : ℝ)|=(4219276491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84385531/200000000 : ℝ)|^4383 ≤ (32433275140863/100000000000000 : ℝ)^3359
        have hw : |(84385531/200000000 : ℝ)|=(84385531/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_12 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-941767201/5000000000 : ℝ)*x 0 + (341719129/625000000 : ℝ)*x 1 + (2627656629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941767201/5000000000 : ℝ)^4383 ≤ (1415328814143/12500000000000 : ℝ)^3359 := by
    have hnat : (941767201 : ℕ)^4383*12500000000000^3359 ≤ 1415328814143^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941767201 5000000000 1415328814143 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341719129/625000000 : ℝ)^4383 ≤ (5685434434539/12500000000000 : ℝ)^3359 := by
    have hnat : (341719129 : ℕ)^4383*12500000000000^3359 ≤ 5685434434539^3359*625000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341719129 625000000 5685434434539 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627656629/5000000000 : ℝ)^4383 ≤ (8638778799873/20000000000000 : ℝ)^3359 := by
    have hnat : (2627656629 : ℕ)^4383*20000000000000^3359 ≤ 8638778799873^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627656629 5000000000 8638778799873 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941767201/5000000000 : ℝ), (341719129/625000000 : ℝ), (2627656629/5000000000 : ℝ)] ![(1415328814143/12500000000000 : ℝ), (5685434434539/12500000000000 : ℝ), (8638778799873/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941767201/5000000000 : ℝ)|^4383 ≤ (1415328814143/12500000000000 : ℝ)^3359
        have hw : |(-941767201/5000000000 : ℝ)|=(941767201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341719129/625000000 : ℝ)|^4383 ≤ (5685434434539/12500000000000 : ℝ)^3359
        have hw : |(341719129/625000000 : ℝ)|=(341719129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627656629/5000000000 : ℝ)|^4383 ≤ (8638778799873/20000000000000 : ℝ)^3359
        have hw : |(2627656629/5000000000 : ℝ)|=(2627656629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_13 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377860537/10000000000 : ℝ)*x 0 + (-125380117/625000000 : ℝ)*x 1 + (656914177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377860537/10000000000 : ℝ)^4383 ≤ (44512823474389/100000000000000 : ℝ)^3359 := by
    have hnat : (5377860537 : ℕ)^4383*100000000000000^3359 ≤ 44512823474389^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377860537 10000000000 44512823474389 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125380117/625000000 : ℝ)^4383 ≤ (1536660101887/12500000000000 : ℝ)^3359 := by
    have hnat : (125380117 : ℕ)^4383*12500000000000^3359 ≤ 1536660101887^3359*625000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125380117 625000000 1536660101887 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656914177/1250000000 : ℝ)^4383 ≤ (10798473923467/25000000000000 : ℝ)^3359 := by
    have hnat : (656914177 : ℕ)^4383*25000000000000^3359 ≤ 10798473923467^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656914177 1250000000 10798473923467 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377860537/10000000000 : ℝ), (-125380117/625000000 : ℝ), (656914177/1250000000 : ℝ)] ![(44512823474389/100000000000000 : ℝ), (1536660101887/12500000000000 : ℝ), (10798473923467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377860537/10000000000 : ℝ)|^4383 ≤ (44512823474389/100000000000000 : ℝ)^3359
        have hw : |(5377860537/10000000000 : ℝ)|=(5377860537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125380117/625000000 : ℝ)|^4383 ≤ (1536660101887/12500000000000 : ℝ)^3359
        have hw : |(-125380117/625000000 : ℝ)|=(125380117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656914177/1250000000 : ℝ)|^4383 ≤ (10798473923467/25000000000000 : ℝ)^3359
        have hw : |(656914177/1250000000 : ℝ)|=(656914177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_14 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688930269/5000000000 : ℝ)*x 0 + (5255313433/10000000000 : ℝ)*x 1 + (-2006081847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688930269/5000000000 : ℝ)^4383 ≤ (44512823485189/100000000000000 : ℝ)^3359 := by
    have hnat : (2688930269 : ℕ)^4383*100000000000000^3359 ≤ 44512823485189^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688930269 5000000000 44512823485189 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255313433/10000000000 : ℝ)^4383 ≤ (10798473969047/25000000000000 : ℝ)^3359 := by
    have hnat : (5255313433 : ℕ)^4383*25000000000000^3359 ≤ 10798473969047^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255313433 10000000000 10798473969047 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006081847/10000000000 : ℝ)^4383 ≤ (1536660076899/12500000000000 : ℝ)^3359 := by
    have hnat : (2006081847 : ℕ)^4383*12500000000000^3359 ≤ 1536660076899^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006081847 10000000000 1536660076899 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688930269/5000000000 : ℝ), (5255313433/10000000000 : ℝ), (-2006081847/10000000000 : ℝ)] ![(44512823485189/100000000000000 : ℝ), (10798473969047/25000000000000 : ℝ), (1536660076899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688930269/5000000000 : ℝ)|^4383 ≤ (44512823485189/100000000000000 : ℝ)^3359
        have hw : |(2688930269/5000000000 : ℝ)|=(2688930269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255313433/10000000000 : ℝ)|^4383 ≤ (10798473969047/25000000000000 : ℝ)^3359
        have hw : |(5255313433/10000000000 : ℝ)|=(5255313433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006081847/10000000000 : ℝ)|^4383 ≤ (1536660076899/12500000000000 : ℝ)^3359
        have hw : |(-2006081847/10000000000 : ℝ)|=(2006081847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_box_15 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82614973/200000000 : ℝ)*x 0 + (4396870307/10000000000 : ℝ)*x 1 + (879374151/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82614973/200000000 : ℝ)^4383 ≤ (15774083400523/50000000000000 : ℝ)^3359 := by
    have hnat : (82614973 : ℕ)^4383*50000000000000^3359 ≤ 15774083400523^3359*200000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82614973 200000000 15774083400523 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4396870307/10000000000 : ℝ)^4383 ≤ (855647857883/2500000000000 : ℝ)^3359 := by
    have hnat : (4396870307 : ℕ)^4383*2500000000000^3359 ≤ 855647857883^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396870307 10000000000 855647857883 2500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879374151/2000000000 : ℝ)^4383 ≤ (17112959432867/50000000000000 : ℝ)^3359 := by
    have hnat : (879374151 : ℕ)^4383*50000000000000^3359 ≤ 17112959432867^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879374151 2000000000 17112959432867 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82614973/200000000 : ℝ), (4396870307/10000000000 : ℝ), (879374151/2000000000 : ℝ)] ![(15774083400523/50000000000000 : ℝ), (855647857883/2500000000000 : ℝ), (17112959432867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82614973/200000000 : ℝ)|^4383 ≤ (15774083400523/50000000000000 : ℝ)^3359
        have hw : |(82614973/200000000 : ℝ)|=(82614973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4396870307/10000000000 : ℝ)|^4383 ≤ (855647857883/2500000000000 : ℝ)^3359
        have hw : |(4396870307/10000000000 : ℝ)|=(4396870307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879374151/2000000000 : ℝ)|^4383 ≤ (17112959432867/50000000000000 : ℝ)^3359
        have hw : |(879374151/2000000000 : ℝ)|=(879374151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(3931/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59101/100000 : ℝ) ∧ (16083/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42331/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (354/3125 : ℝ) ^ (2191/512 : ℝ) ≤ (2240685614064297/25000000000000000000 : ℝ) := by
    have hpowers : (354/3125 : ℝ)^2191 ≤ (2240685614064297/25000000000000000000 : ℝ)^512 := by
      have hnat : (354 : ℕ)^2191*25000000000000000000^512 ≤ 2240685614064297^512*3125^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        354 3125 2240685614064297 25000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (354/3125 : ℝ)) (X := (2240685614064297/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (2191/512 : ℝ) ≤ (5551652092526573/20000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^2191 ≤ (5551652092526573/20000000000000000000 : ℝ)^512 := by
      have hnat : (14753 : ℕ)^2191*20000000000000000000^512 ≤ 5551652092526573^512*100000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 5551652092526573 20000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (5551652092526573/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502240685614064297/12500000000000000000 : ℝ) ≤ (31251308936841/31250000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (12502240685614064297/12500000000000000000 : ℝ)^512 ≤ (31251308936841/31250000000000 : ℝ)^2191 := by
      have hnat : (12502240685614064297 : ℕ)^512*31250000000000^2191 ≤ 31251308936841^2191*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502240685614064297 12500000000000000000 31251308936841 31250000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31251308936841/31250000000000 : ℝ)) (X := (12502240685614064297/12500000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036721002918890053/100000000000000000000 : ℝ) ≤ (5000428993809939/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (100036721002918890053/100000000000000000000 : ℝ)^512 ≤ (5000428993809939/5000000000000000 : ℝ)^2191 := by
      have hnat : (100036721002918890053 : ℕ)^512*5000000000000000^2191 ≤ 5000428993809939^2191*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036721002918890053 100000000000000000000 5000428993809939 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000428993809939/5000000000000000 : ℝ)) (X := (100036721002918890053/100000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005551652092526573/10000000000000000000 : ℝ) ≤ (2500324278862659/2500000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (10005551652092526573/10000000000000000000 : ℝ)^512 ≤ (2500324278862659/2500000000000000 : ℝ)^2191 := by
      have hnat : (10005551652092526573 : ℕ)^512*2500000000000000^2191 ≤ 2500324278862659^2191*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005551652092526573 10000000000000000000 2500324278862659 2500000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500324278862659/2500000000000000 : ℝ)) (X := (10005551652092526573/10000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2240685614064297/25000000000000000000 : ℝ) ≤ ((535023214291313793/535156250000000000 : ℝ)+2*(219563915379/171250000000000 : ℝ)*(354/3125 : ℝ))^(2191/512 : ℝ) := by
    rw [show (535023214291313793/535156250000000000 : ℝ)+2*(219563915379/171250000000000 : ℝ)*(354/3125 : ℝ)=(31251308936841/31250000000000 : ℝ) by norm_num, show 1+2*(2240685614064297/25000000000000000000 : ℝ)=(12502240685614064297/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5551652092526573/20000000000000000000 : ℝ)+(2240685614064297/25000000000000000000 : ℝ) ≤ ((535023214291313793/535156250000000000 : ℝ)+(219563915379/171250000000000 : ℝ)*((14753/100000 : ℝ)+(354/3125 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (535023214291313793/535156250000000000 : ℝ)+(219563915379/171250000000000 : ℝ)*((14753/100000 : ℝ)+(354/3125 : ℝ))=(5000428993809939/5000000000000000 : ℝ) by norm_num, show 1+(5551652092526573/20000000000000000000 : ℝ)+(2240685614064297/25000000000000000000 : ℝ)=(100036721002918890053/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5551652092526573/20000000000000000000 : ℝ) ≤ ((535023214291313793/535156250000000000 : ℝ)+2*(219563915379/171250000000000 : ℝ)*(14753/100000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (535023214291313793/535156250000000000 : ℝ)+2*(219563915379/171250000000000 : ℝ)*(14753/100000 : ℝ)=(2500324278862659/2500000000000000 : ℝ) by norm_num, show 1+2*(5551652092526573/20000000000000000000 : ℝ)=(10005551652092526573/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (535023214291313793/535156250000000000 : ℝ)*(X 1 0+X 2 0)+(219563915379/171250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (535023214291313793/535156250000000000 : ℝ)) (alpha := (219563915379/171250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (535023214291313793/535156250000000000 : ℝ)*(X 0 1+X 2 1)+(219563915379/171250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (535023214291313793/535156250000000000 : ℝ)) (alpha := (219563915379/171250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (535023214291313793/535156250000000000 : ℝ)*(X 0 2+X 1 2)+(219563915379/171250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (535023214291313793/535156250000000000 : ℝ)) (alpha := (219563915379/171250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22686481/125000000 : ℝ)*X 0 0+(538651251/1000000000 : ℝ)*X 0 1+(5386512001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286020587/10000000000 : ℝ)*X 1 0+(-1952955479/10000000000 : ℝ)*X 1 1+(673314013/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321505083/2500000000 : ℝ)*X 2 0+(5386512257/10000000000 : ℝ)*X 2 1+(-61029863/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4452294331/10000000000 : ℝ)*X 0 0+(1059097323/2500000000 : ℝ)*X 0 1+(2118194709/5000000000 : ℝ)*X 0 2+(4452294331/10000000000 : ℝ)*X 1 0+(1059097323/2500000000 : ℝ)*X 1 1+(2118194709/5000000000 : ℝ)*X 1 2+(4452294331/10000000000 : ℝ)*X 2 0+(1059097323/2500000000 : ℝ)*X 2 1+(2118194709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1069921067/5000000000 : ℝ)*X 0 0+(5266436151/10000000000 : ℝ)*X 0 1+(1053287257/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370076517/10000000000 : ℝ)*X 1 0+(-500417353/2500000000 : ℝ)*X 1 1+(5266435759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370075901/10000000000 : ℝ)*X 2 0+(1316609227/2500000000 : ℝ)*X 2 1+(-2001668701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4158420473/10000000000 : ℝ)*X 0 0+(876654981/2000000000 : ℝ)*X 0 1+(2191637767/5000000000 : ℝ)*X 0 2+(4158420473/10000000000 : ℝ)*X 1 0+(876654981/2000000000 : ℝ)*X 1 1+(2191637767/5000000000 : ℝ)*X 1 2+(4158420473/10000000000 : ℝ)*X 2 0+(876654981/2000000000 : ℝ)*X 2 1+(2191637767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-41428331/200000000 : ℝ)*X 0 0+(2591703569/5000000000 : ℝ)*X 0 1+(540048981/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638115847/5000000000 : ℝ)*X 1 0+(-1947158161/10000000000 : ℝ)*X 1 1+(5400489807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276231709/10000000000 : ℝ)*X 2 0+(5400489747/10000000000 : ℝ)*X 2 1+(-1947158221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4485945789/10000000000 : ℝ)*X 0 0+(4219276491/10000000000 : ℝ)*X 0 1+(84385531/200000000 : ℝ)*X 0 2+(4485945789/10000000000 : ℝ)*X 1 0+(4219276491/10000000000 : ℝ)*X 1 1+(84385531/200000000 : ℝ)*X 1 2+(4485945789/10000000000 : ℝ)*X 2 0+(4219276491/10000000000 : ℝ)*X 2 1+(84385531/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-941767201/5000000000 : ℝ)*X 0 0+(341719129/625000000 : ℝ)*X 0 1+(2627656629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5377860537/10000000000 : ℝ)*X 1 0+(-125380117/625000000 : ℝ)*X 1 1+(656914177/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688930269/5000000000 : ℝ)*X 2 0+(5255313433/10000000000 : ℝ)*X 2 1+(-2006081847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((82614973/200000000 : ℝ)*X 0 0+(4396870307/10000000000 : ℝ)*X 0 1+(879374151/2000000000 : ℝ)*X 0 2+(82614973/200000000 : ℝ)*X 1 0+(4396870307/10000000000 : ℝ)*X 1 1+(879374151/2000000000 : ℝ)*X 1 2+(82614973/200000000 : ℝ)*X 2 0+(4396870307/10000000000 : ℝ)*X 2 1+(879374151/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3931/6250 : ℝ) ≤ (-16828864618231048947478992120843/26757812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (19907121/25000000000000 : ℝ)*(lower1) + (4167851/5000000000000 : ℝ)*(lower2) + (75331623/50000000000000 : ℝ)*(lower3) + (658741/4000000000000 : ℝ)*(lower4) + (3010278045089383/100000000000000 : ℝ)*(major0) + (3010278045089383/100000000000000 : ℝ)*(major1) + (3010278045089383/100000000000000 : ℝ)*(major2) + (2439923827/20000000000000 : ℝ)*(sp1) + (2067712258163021/50000000000000 : ℝ)*(sp4) + (2067706158353453/50000000000000 : ℝ)*(sp5) + (2067571541509343/50000000000000 : ℝ)*(sp6) + (476515444248489/25000000000000 : ℝ)*(sp7) + (70358326839/25000000000000 : ℝ)*(sp14) + (34221881959/100000000000000 : ℝ)*(sp15) + (381219199775183/20000000000000 : ℝ)*(f.failure) + (2067712258163021/50000000000000 : ℝ)*(f.sum) + (979308889641/4281250000000000000000000000 : ℝ)*base65 + (248438300859031/53515625000000000000000000000000 : ℝ)*base68 + (113444987132109031/53515625000000000000000000000000 : ℝ)*base70 + (712632386210859719/53515625000000000000000000000000 : ℝ)*base71 + (24272624483343/8562500000000000000000000000 : ℝ)*base74 + (139741302638203469/53515625000000000000000000000000 : ℝ)*base75 + (63623405848593707/6689453125000000000000000000000 : ℝ)*base78 + (17214587550077781/53515625000000000000000000000000 : ℝ)*base80 + (295927047601061/17125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2450509/250000000000000000000 : ℝ)*base89 + (2450509/250000000000000000000 : ℝ)*base91 + (2450509/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59101/100000 : ℝ) ≤ (158148428954891741654740084947/267578125000000000000000000000 : ℝ) := by norm_num
    linear_combination (25581547/100000000000000 : ℝ)*(lower1) + (37729433/50000000000000 : ℝ)*(upper2) + (5840141/50000000000000 : ℝ)*(upper3) + (4060897/6250000000000 : ℝ)*(lower5) + (30816931901509/1000000000000 : ℝ)*(major0) + (30816931901509/1000000000000 : ℝ)*(major1) + (30816931901509/1000000000000 : ℝ)*(major2) + (2096182573601661/50000000000000 : ℝ)*(sp0) + (104809234554597/2500000000000 : ℝ)*(sp1) + (4192365641021587/100000000000000 : ℝ)*(sp2) + (390262559178713/20000000000000 : ℝ)*(sp3) + (3741162293/100000000000000 : ℝ)*(sp6) + (2986743839/100000000000000 : ℝ)*(sp7) + (2117490279/50000000000000 : ℝ)*(sp8) + (487828945659351/25000000000000 : ℝ)*(f.failure) + (104809234554597/2500000000000 : ℝ)*(f.sum) + (1101452514959/342500000000000000000000000 : ℝ)*base65 + (1992467121804827/2140625000000000000000000000000 : ℝ)*base68 + (1779446377667899/1070312500000000000000000000000 : ℝ)*base69 + (14732502087863351/1070312500000000000000000000000 : ℝ)*base72 + (141180143113/685000000000000000000000000 : ℝ)*base73 + (2859850263767613/535156250000000000000000000000 : ℝ)*base76 + (14058006260554827/2140625000000000000000000000000 : ℝ)*base78 + (948305693894601/1070312500000000000000000000000 : ℝ)*base80 + (957995750753/685000000000000000000000000 : ℝ)*base81 + (1691173/312500000000000000000 : ℝ)*base89 + (1691173/312500000000000000000 : ℝ)*base91 + (1691173/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16083/20000 : ℝ) ≤ (43036133631783196468143574651563/53515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11314471/100000000000000 : ℝ)*(upper0) + (6100267/25000000000000 : ℝ)*(lower1) + (31449063/100000000000000 : ℝ)*(lower3) + (78047351/100000000000000 : ℝ)*(lower5) + (1694956233117209/50000000000000 : ℝ)*(major0) + (1694956233117209/50000000000000 : ℝ)*(major1) + (1694956233117209/50000000000000 : ℝ)*(major2) + (1502591339/50000000000000 : ℝ)*(sp0) + (7058826801/100000000000000 : ℝ)*(sp1) + (5692887911/100000000000000 : ℝ)*(sp3) + (2303268486094269/50000000000000 : ℝ)*(sp8) + (921306583708883/20000000000000 : ℝ)*(sp9) + (287908748585701/6250000000000 : ℝ)*(sp10) + (67077290644651/3125000000000 : ℝ)*(sp11) + (268309874189593/12500000000000 : ℝ)*(f.failure) + (287908748585701/6250000000000 : ℝ)*(f.sum) + (10214227360281/17125000000000000000000000000 : ℝ)*base66 + (66645990367214681/13378906250000000000000000000000 : ℝ)*base67 + (18679580000872111/3344726562500000000000000000000 : ℝ)*base70 + (132213447665180013/26757812500000000000000000000000 : ℝ)*base72 + (32021588942453/8562500000000000000000000000 : ℝ)*base74 + (1101514578016688151/53515625000000000000000000000000 : ℝ)*base76 + (232320032728406901/53515625000000000000000000000000 : ℝ)*base78 + (184712034724191569/13378906250000000000000000000000 : ℝ)*base80 + (6942237353953/8562500000000000000000000000 : ℝ)*base82 + (2607939/156250000000000000000 : ℝ)*base89 + (2607939/156250000000000000000 : ℝ)*base91 + (2607939/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42331/50000 : ℝ) ≤ (-45306181247140988127446653678677/53515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5355101/20000000000000 : ℝ)*(lower1) + (22393431/50000000000000 : ℝ)*(upper3) + (35442279/100000000000000 : ℝ)*(lower4) + (73688421/50000000000000 : ℝ)*(upper5) + (1713660851595611/50000000000000 : ℝ)*(major0) + (1713660851595611/50000000000000 : ℝ)*(major1) + (1713660851595611/50000000000000 : ℝ)*(major2) + (651406747/25000000000000 : ℝ)*(sp4) + (5766734597/12500000000000 : ℝ)*(sp6) + (20353677929/50000000000000 : ℝ)*(sp7) + (4712694336774349/100000000000000 : ℝ)*(sp12) + (4712696942401337/100000000000000 : ℝ)*(sp13) + (4712650808524561/100000000000000 : ℝ)*(sp14) + (2170125665139277/100000000000000 : ℝ)*(sp15) + (434033274499027/20000000000000 : ℝ)*(f.failure) + (4712696942401337/100000000000000 : ℝ)*(f.sum) + (12435105557987/8562500000000000000000000000 : ℝ)*base66 + (472940825024228171/53515625000000000000000000000000 : ℝ)*base67 + (68493550371084329/53515625000000000000000000000000 : ℝ)*base70 + (277295309946103171/53515625000000000000000000000000 : ℝ)*base71 + (116690838681849/17125000000000000000000000000 : ℝ)*base74 + (597243041781259421/53515625000000000000000000000000 : ℝ)*base75 + (62695309186918773/26757812500000000000000000000000 : ℝ)*base77 + (193588850678325023/26757812500000000000000000000000 : ℝ)*base79 + (9120039198507/535156250000000000000000000 : ℝ)*base82 + (387321/250000000000000000000 : ℝ)*base89 + (387321/250000000000000000000 : ℝ)*base91 + (387321/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1423_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3931/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59101/100000 : ℝ) else (16083/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42331/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1423_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1423_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3931/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59101/100000 : ℝ) else (16083/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42331/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1423_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1423_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1423_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3931/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59101/100000 : ℝ) else (16083/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42331/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1423_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
