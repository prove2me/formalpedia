-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1342_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:14.764573+00:00
-- url     : https://prove2.me/submissions/3deb088f-b42e-4675-9e4b-cd9274155fc4

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
theorem support_rectangle_w1342_s3_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021105331/5000000000 : ℝ)*x 0 + (5427167947/10000000000 : ℝ)*x 1 + (5231303687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021105331/5000000000 : ℝ)^2151 ≤ (1554160599083/12500000000000 : ℝ)^1639 := by
    have hnat : (1021105331 : ℕ)^2151*12500000000000^1639 ≤ 1554160599083^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021105331 5000000000 1554160599083 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427167947/10000000000 : ℝ)^2151 ≤ (44839191171827/100000000000000 : ℝ)^1639 := by
    have hnat : (5427167947 : ℕ)^2151*100000000000000^1639 ≤ 44839191171827^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427167947 10000000000 44839191171827 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231303687/10000000000 : ℝ)^2151 ≤ (42727524018943/100000000000000 : ℝ)^1639 := by
    have hnat : (5231303687 : ℕ)^2151*100000000000000^1639 ≤ 42727524018943^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231303687 10000000000 42727524018943 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021105331/5000000000 : ℝ), (5427167947/10000000000 : ℝ), (5231303687/10000000000 : ℝ)] ![(1554160599083/12500000000000 : ℝ), (44839191171827/100000000000000 : ℝ), (42727524018943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021105331/5000000000 : ℝ)|^2151 ≤ (1554160599083/12500000000000 : ℝ)^1639
        have hw : |(-1021105331/5000000000 : ℝ)|=(1021105331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427167947/10000000000 : ℝ)|^2151 ≤ (44839191171827/100000000000000 : ℝ)^1639
        have hw : |(5427167947/10000000000 : ℝ)|=(5427167947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231303687/10000000000 : ℝ)|^2151 ≤ (42727524018943/100000000000000 : ℝ)^1639
        have hw : |(5231303687/10000000000 : ℝ)|=(5231303687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s3_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (669085759/1250000000 : ℝ)*x 0 + (-2142311967/10000000000 : ℝ)*x 1 + (1046260709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669085759/1250000000 : ℝ)^2151 ≤ (11008331830851/25000000000000 : ℝ)^1639 := by
    have hnat : (669085759 : ℕ)^2151*25000000000000^1639 ≤ 11008331830851^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669085759 1250000000 11008331830851 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142311967/10000000000 : ℝ)^2151 ≤ (6619575082833/50000000000000 : ℝ)^1639 := by
    have hnat : (2142311967 : ℕ)^2151*50000000000000^1639 ≤ 6619575082833^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142311967 10000000000 6619575082833 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046260709/2000000000 : ℝ)^2151 ≤ (42727522496827/100000000000000 : ℝ)^1639 := by
    have hnat : (1046260709 : ℕ)^2151*100000000000000^1639 ≤ 42727522496827^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046260709 2000000000 42727522496827 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669085759/1250000000 : ℝ), (-2142311967/10000000000 : ℝ), (1046260709/2000000000 : ℝ)] ![(11008331830851/25000000000000 : ℝ), (6619575082833/50000000000000 : ℝ), (42727522496827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669085759/1250000000 : ℝ)|^2151 ≤ (11008331830851/25000000000000 : ℝ)^1639
        have hw : |(669085759/1250000000 : ℝ)|=(669085759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142311967/10000000000 : ℝ)|^2151 ≤ (6619575082833/50000000000000 : ℝ)^1639
        have hw : |(-2142311967/10000000000 : ℝ)|=(2142311967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046260709/2000000000 : ℝ)|^2151 ≤ (42727522496827/100000000000000 : ℝ)^1639
        have hw : |(1046260709/2000000000 : ℝ)|=(1046260709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s3_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676343101/5000000000 : ℝ)*x 0 + (653912913/1250000000 : ℝ)*x 1 + (-2142312113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676343101/5000000000 : ℝ)^2151 ≤ (44033328726911/100000000000000 : ℝ)^1639 := by
    have hnat : (2676343101 : ℕ)^2151*100000000000000^1639 ≤ 44033328726911^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676343101 5000000000 44033328726911 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653912913/1250000000 : ℝ)^2151 ≤ (42727519913519/100000000000000 : ℝ)^1639 := by
    have hnat : (653912913 : ℕ)^2151*100000000000000^1639 ≤ 42727519913519^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653912913 1250000000 42727519913519 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142312113/10000000000 : ℝ)^2151 ≤ (529566053991/4000000000000 : ℝ)^1639 := by
    have hnat : (2142312113 : ℕ)^2151*4000000000000^1639 ≤ 529566053991^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142312113 10000000000 529566053991 4000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676343101/5000000000 : ℝ), (653912913/1250000000 : ℝ), (-2142312113/10000000000 : ℝ)] ![(44033328726911/100000000000000 : ℝ), (42727519913519/100000000000000 : ℝ), (529566053991/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676343101/5000000000 : ℝ)|^2151 ≤ (44033328726911/100000000000000 : ℝ)^1639
        have hw : |(2676343101/5000000000 : ℝ)|=(2676343101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653912913/1250000000 : ℝ)|^2151 ≤ (42727519913519/100000000000000 : ℝ)^1639
        have hw : |(653912913/1250000000 : ℝ)|=(653912913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142312113/10000000000 : ℝ)|^2151 ≤ (529566053991/4000000000000 : ℝ)^1639
        have hw : |(-2142312113/10000000000 : ℝ)|=(2142312113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s3_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4325555019/10000000000 : ℝ)*x 0 + (4124971781/10000000000 : ℝ)*x 1 + (1133805943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325555019/10000000000 : ℝ)^2151 ≤ (33292511006371/100000000000000 : ℝ)^1639 := by
    have hnat : (4325555019 : ℕ)^2151*100000000000000^1639 ≤ 33292511006371^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325555019 10000000000 33292511006371 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124971781/10000000000 : ℝ)^2151 ≤ (31281245319843/100000000000000 : ℝ)^1639 := by
    have hnat : (4124971781 : ℕ)^2151*100000000000000^1639 ≤ 31281245319843^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124971781 10000000000 31281245319843 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133805943/2500000000 : ℝ)^2151 ≤ (7085248731009/20000000000000 : ℝ)^1639 := by
    have hnat : (1133805943 : ℕ)^2151*20000000000000^1639 ≤ 7085248731009^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133805943 2500000000 7085248731009 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325555019/10000000000 : ℝ), (4124971781/10000000000 : ℝ), (1133805943/2500000000 : ℝ)] ![(33292511006371/100000000000000 : ℝ), (31281245319843/100000000000000 : ℝ), (7085248731009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325555019/10000000000 : ℝ)|^2151 ≤ (33292511006371/100000000000000 : ℝ)^1639
        have hw : |(4325555019/10000000000 : ℝ)|=(4325555019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124971781/10000000000 : ℝ)|^2151 ≤ (31281245319843/100000000000000 : ℝ)^1639
        have hw : |(4124971781/10000000000 : ℝ)|=(4124971781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133805943/2500000000 : ℝ)|^2151 ≤ (7085248731009/20000000000000 : ℝ)^1639
        have hw : |(1133805943/2500000000 : ℝ)|=(1133805943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s3_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-255278753/1250000000 : ℝ)*x 0 + (2616059901/5000000000 : ℝ)*x 1 + (5426346843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255278753/1250000000 : ℝ)^2151 ≤ (155417993691/1250000000000 : ℝ)^1639 := by
    have hnat : (255278753 : ℕ)^2151*1250000000000^1639 ≤ 155417993691^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255278753 1250000000 155417993691 1250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616059901/5000000000 : ℝ)^2151 ≤ (21368136134553/50000000000000 : ℝ)^1639 := by
    have hnat : (2616059901 : ℕ)^2151*50000000000000^1639 ≤ 21368136134553^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616059901 5000000000 21368136134553 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426346843/10000000000 : ℝ)^2151 ≤ (44830288223147/100000000000000 : ℝ)^1639 := by
    have hnat : (5426346843 : ℕ)^2151*100000000000000^1639 ≤ 44830288223147^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426346843 10000000000 44830288223147 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-255278753/1250000000 : ℝ), (2616059901/5000000000 : ℝ), (5426346843/10000000000 : ℝ)] ![(155417993691/1250000000000 : ℝ), (21368136134553/50000000000000 : ℝ), (44830288223147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-255278753/1250000000 : ℝ)|^2151 ≤ (155417993691/1250000000000 : ℝ)^1639
        have hw : |(-255278753/1250000000 : ℝ)|=(255278753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616059901/5000000000 : ℝ)|^2151 ≤ (21368136134553/50000000000000 : ℝ)^1639
        have hw : |(2616059901/5000000000 : ℝ)|=(2616059901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426346843/10000000000 : ℝ)|^2151 ≤ (44830288223147/100000000000000 : ℝ)^1639
        have hw : |(5426346843/10000000000 : ℝ)|=(5426346843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s3_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302234131/10000000000 : ℝ)*x 0 + (-19472687/100000000 : ℝ)*x 1 + (5426347179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302234131/10000000000 : ℝ)^2151 ≤ (43489441376457/100000000000000 : ℝ)^1639 := by
    have hnat : (5302234131 : ℕ)^2151*100000000000000^1639 ≤ 43489441376457^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302234131 10000000000 43489441376457 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19472687/100000000 : ℝ)^2151 ≤ (1460033341913/12500000000000 : ℝ)^1639 := by
    have hnat : (19472687 : ℕ)^2151*12500000000000^1639 ≤ 1460033341913^1639*100000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19472687 100000000 1460033341913 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426347179/10000000000 : ℝ)^2151 ≤ (44830291866193/100000000000000 : ℝ)^1639 := by
    have hnat : (5426347179 : ℕ)^2151*100000000000000^1639 ≤ 44830291866193^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426347179 10000000000 44830291866193 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302234131/10000000000 : ℝ), (-19472687/100000000 : ℝ), (5426347179/10000000000 : ℝ)] ![(43489441376457/100000000000000 : ℝ), (1460033341913/12500000000000 : ℝ), (44830291866193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302234131/10000000000 : ℝ)|^2151 ≤ (43489441376457/100000000000000 : ℝ)^1639
        have hw : |(5302234131/10000000000 : ℝ)|=(5302234131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19472687/100000000 : ℝ)|^2151 ≤ (1460033341913/12500000000000 : ℝ)^1639
        have hw : |(-19472687/100000000 : ℝ)|=(19472687/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426347179/10000000000 : ℝ)|^2151 ≤ (44830291866193/100000000000000 : ℝ)^1639
        have hw : |(5426347179/10000000000 : ℝ)|=(5426347179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s3_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302235123/10000000000 : ℝ)*x 0 + (678293317/1250000000 : ℝ)*x 1 + (-1947268231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302235123/10000000000 : ℝ)^2151 ≤ (21744726027329/50000000000000 : ℝ)^1639 := by
    have hnat : (5302235123 : ℕ)^2151*50000000000000^1639 ≤ 21744726027329^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302235123 10000000000 21744726027329 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678293317/1250000000 : ℝ)^2151 ≤ (4483028489453/10000000000000 : ℝ)^1639 := by
    have hnat : (678293317 : ℕ)^2151*10000000000000^1639 ≤ 4483028489453^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678293317 1250000000 4483028489453 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947268231/10000000000 : ℝ)^2151 ≤ (2920065760827/25000000000000 : ℝ)^1639 := by
    have hnat : (1947268231 : ℕ)^2151*25000000000000^1639 ≤ 2920065760827^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947268231 10000000000 2920065760827 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302235123/10000000000 : ℝ), (678293317/1250000000 : ℝ), (-1947268231/10000000000 : ℝ)] ![(21744726027329/50000000000000 : ℝ), (4483028489453/10000000000000 : ℝ), (2920065760827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302235123/10000000000 : ℝ)|^2151 ≤ (21744726027329/50000000000000 : ℝ)^1639
        have hw : |(5302235123/10000000000 : ℝ)|=(5302235123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678293317/1250000000 : ℝ)|^2151 ≤ (4483028489453/10000000000000 : ℝ)^1639
        have hw : |(678293317/1250000000 : ℝ)|=(678293317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947268231/10000000000 : ℝ)|^2151 ≤ (2920065760827/25000000000000 : ℝ)^1639
        have hw : |(-1947268231/10000000000 : ℝ)|=(1947268231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s3_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4325595971/10000000000 : ℝ)*x 0 + (2266757029/5000000000 : ℝ)*x 1 + (4126691113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325595971/10000000000 : ℝ)^2151 ≤ (33292924664847/100000000000000 : ℝ)^1639 := by
    have hnat : (4325595971 : ℕ)^2151*100000000000000^1639 ≤ 33292924664847^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325595971 10000000000 33292924664847 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266757029/5000000000 : ℝ)^2151 ≤ (1416348701477/4000000000000 : ℝ)^1639 := by
    have hnat : (2266757029 : ℕ)^2151*4000000000000^1639 ≤ 1416348701477^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266757029 5000000000 1416348701477 4000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4126691113/10000000000 : ℝ)^2151 ≤ (31298357782979/100000000000000 : ℝ)^1639 := by
    have hnat : (4126691113 : ℕ)^2151*100000000000000^1639 ≤ 31298357782979^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126691113 10000000000 31298357782979 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325595971/10000000000 : ℝ), (2266757029/5000000000 : ℝ), (4126691113/10000000000 : ℝ)] ![(33292924664847/100000000000000 : ℝ), (1416348701477/4000000000000 : ℝ), (31298357782979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325595971/10000000000 : ℝ)|^2151 ≤ (33292924664847/100000000000000 : ℝ)^1639
        have hw : |(4325595971/10000000000 : ℝ)|=(4325595971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266757029/5000000000 : ℝ)|^2151 ≤ (1416348701477/4000000000000 : ℝ)^1639
        have hw : |(2266757029/5000000000 : ℝ)|=(2266757029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4126691113/10000000000 : ℝ)|^2151 ≤ (31298357782979/100000000000000 : ℝ)^1639
        have hw : |(4126691113/10000000000 : ℝ)|=(4126691113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2463/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2173/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2013/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2463/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2013/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2463/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2013/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2463/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2013/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2463/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2013/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2463/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2013/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2463/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2463/25000 : ℝ) ^ (4301/1024 : ℝ) ≤ (2961937705706003/50000000000000000000 : ℝ) := by
    have hpowers : (2463/25000 : ℝ)^4301 ≤ (2961937705706003/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2463 : ℕ)^4301*50000000000000000000^1024 ≤ 2961937705706003^1024*25000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2463 25000 2961937705706003 50000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2463/25000 : ℝ)) (X := (2961937705706003/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2013/12500 : ℝ) ^ (4301/1024 : ℝ) ≤ (46662381941827923/100000000000000000000 : ℝ) := by
    have hpowers : (2013/12500 : ℝ)^4301 ≤ (46662381941827923/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2013 : ℕ)^4301*100000000000000000000^1024 ≤ 46662381941827923^1024*12500^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2013 12500 46662381941827923 100000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2013/12500 : ℝ)) (X := (46662381941827923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002961937705706003/25000000000000000000 : ℝ) ≤ (2500070515864329/2500000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (25002961937705706003/25000000000000000000 : ℝ)^1024 ≤ (2500070515864329/2500000000000000 : ℝ)^4301 := by
      have hnat : (25002961937705706003 : ℕ)^1024*2500000000000000^4301 ≤ 2500070515864329^4301*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002961937705706003 25000000000000000000 2500070515864329 2500000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070515864329/2500000000000000 : ℝ)) (X := (25002961937705706003/25000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052586257353239929/100000000000000000000 : ℝ) ≤ (10001251744788267/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (100052586257353239929/100000000000000000000 : ℝ)^1024 ≤ (10001251744788267/10000000000000000 : ℝ)^4301 := by
      have hnat : (100052586257353239929 : ℕ)^1024*10000000000000000^4301 ≤ 10001251744788267^4301*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052586257353239929 100000000000000000000 10001251744788267 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001251744788267/10000000000000000 : ℝ)) (X := (100052586257353239929/100000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046662381941827923/50000000000000000000 : ℝ) ≤ (5001110713059609/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (50046662381941827923/50000000000000000000 : ℝ)^1024 ≤ (5001110713059609/5000000000000000 : ℝ)^4301 := by
      have hnat : (50046662381941827923 : ℕ)^1024*5000000000000000^4301 ≤ 5001110713059609^4301*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046662381941827923 50000000000000000000 5001110713059609 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001110713059609/5000000000000000 : ℝ)) (X := (50046662381941827923/50000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2961937705706003/50000000000000000000 : ℝ) ≤ ((2604277369157920047/2605000000000000000 : ℝ)+2*(323227110317/208400000000000 : ℝ)*(2463/25000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (2604277369157920047/2605000000000000000 : ℝ)+2*(323227110317/208400000000000 : ℝ)*(2463/25000 : ℝ)=(2500070515864329/2500000000000000 : ℝ) by norm_num, show 1+2*(2961937705706003/50000000000000000000 : ℝ)=(25002961937705706003/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46662381941827923/100000000000000000000 : ℝ)+(2961937705706003/50000000000000000000 : ℝ) ≤ ((2604277369157920047/2605000000000000000 : ℝ)+(323227110317/208400000000000 : ℝ)*((2013/12500 : ℝ)+(2463/25000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (2604277369157920047/2605000000000000000 : ℝ)+(323227110317/208400000000000 : ℝ)*((2013/12500 : ℝ)+(2463/25000 : ℝ))=(10001251744788267/10000000000000000 : ℝ) by norm_num, show 1+(46662381941827923/100000000000000000000 : ℝ)+(2961937705706003/50000000000000000000 : ℝ)=(100052586257353239929/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46662381941827923/100000000000000000000 : ℝ) ≤ ((2604277369157920047/2605000000000000000 : ℝ)+2*(323227110317/208400000000000 : ℝ)*(2013/12500 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (2604277369157920047/2605000000000000000 : ℝ)+2*(323227110317/208400000000000 : ℝ)*(2013/12500 : ℝ)=(5001110713059609/5000000000000000 : ℝ) by norm_num, show 1+2*(46662381941827923/100000000000000000000 : ℝ)=(50046662381941827923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2604277369157920047/2605000000000000000 : ℝ)*(X 1 0+X 2 0)+(323227110317/208400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2463/25000 : ℝ)) (hi := (2013/12500 : ℝ)) (c := (2604277369157920047/2605000000000000000 : ℝ)) (alpha := (323227110317/208400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2604277369157920047/2605000000000000000 : ℝ)*(X 0 1+X 2 1)+(323227110317/208400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2463/25000 : ℝ)) (hi := (2013/12500 : ℝ)) (c := (2604277369157920047/2605000000000000000 : ℝ)) (alpha := (323227110317/208400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2604277369157920047/2605000000000000000 : ℝ)*(X 0 2+X 1 2)+(323227110317/208400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2463/25000 : ℝ)) (hi := (2013/12500 : ℝ)) (c := (2604277369157920047/2605000000000000000 : ℝ)) (alpha := (323227110317/208400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1021105331/5000000000 : ℝ)*X 0 0+(5427167947/10000000000 : ℝ)*X 0 1+(5231303687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669085759/1250000000 : ℝ)*X 1 0+(-2142311967/10000000000 : ℝ)*X 1 1+(1046260709/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676343101/5000000000 : ℝ)*X 2 0+(653912913/1250000000 : ℝ)*X 2 1+(-2142312113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325555019/10000000000 : ℝ)*X 0 0+(4124971781/10000000000 : ℝ)*X 0 1+(1133805943/2500000000 : ℝ)*X 0 2+(4325555019/10000000000 : ℝ)*X 1 0+(4124971781/10000000000 : ℝ)*X 1 1+(1133805943/2500000000 : ℝ)*X 1 2+(4325555019/10000000000 : ℝ)*X 2 0+(4124971781/10000000000 : ℝ)*X 2 1+(1133805943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-255278753/1250000000 : ℝ)*X 0 0+(2616059901/5000000000 : ℝ)*X 0 1+(5426346843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302234131/10000000000 : ℝ)*X 1 0+(-19472687/100000000 : ℝ)*X 1 1+(5426347179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302235123/10000000000 : ℝ)*X 2 0+(678293317/1250000000 : ℝ)*X 2 1+(-1947268231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325595971/10000000000 : ℝ)*X 0 0+(2266757029/5000000000 : ℝ)*X 0 1+(4126691113/10000000000 : ℝ)*X 0 2+(4325595971/10000000000 : ℝ)*X 1 0+(2266757029/5000000000 : ℝ)*X 1 1+(4126691113/10000000000 : ℝ)*X 1 2+(4325595971/10000000000 : ℝ)*X 2 0+(2266757029/5000000000 : ℝ)*X 2 1+(4126691113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (387122537470614383712462141/130250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582536707/100000000000000 : ℝ)*(base19) + (668254661/100000000000000 : ℝ)*(base23) + (52520193/100000000000000 : ℝ)*(lower2) + (81248003/50000000000000 : ℝ)*(upper3) + (8007431/25000000000000 : ℝ)*(lower4) + (3771558142449/100000000000 : ℝ)*(major0) + (3771558142449/100000000000 : ℝ)*(major1) + (3771558142449001/100000000000000 : ℝ)*(major2) + (2552791482922517/50000000000000 : ℝ)*(sp0) + (5105584577630827/100000000000000 : ℝ)*(sp1) + (5105584491912873/100000000000000 : ℝ)*(sp2) + (1218763665030633/50000000000000 : ℝ)*(sp3) + (2194322501/100000000000000 : ℝ)*(sp4) + (923899381/25000000000000 : ℝ)*(sp7) + (243753102565879/10000000000000 : ℝ)*(f.failure) + (2552792580083767/50000000000000 : ℝ)*(f.sum) + (69483634497523/20840000000000000000000000000 : ℝ)*base66 + (3380266535264869/521000000000000000000000000000 : ℝ)*base68 + (4767117868936976953/260500000000000000000000000000000 : ℝ)*base70 + (6803233546808869/521000000000000000000000000000 : ℝ)*base72 + (7061021964043/20840000000000000000000000000 : ℝ)*base74 + (1048826056083976953/260500000000000000000000000000000 : ℝ)*base76 + (2221042949204397/260500000000000000000000000000 : ℝ)*base78 + (4313460049627397/260500000000000000000000000000 : ℝ)*base80 + (360125521613/104200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (19322859/1000000000000000000000 : ℝ)*base89 + (19322859/1000000000000000000000 : ℝ)*base91 + (9322859/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2689016536784069823152499/4070312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (22124313/10000000000000 : ℝ)*(base19) + (862254477/50000000000000 : ℝ)*(base23) + (89399419/50000000000000 : ℝ)*(upper3) + (166904013/100000000000000 : ℝ)*(lower4) + (30062501/25000000000000 : ℝ)*(upper5) + (118854548471513/3125000000000 : ℝ)*(major0) + (118854548471513/3125000000000 : ℝ)*(major1) + (118854548471513/3125000000000 : ℝ)*(major2) + (611296471/12500000000000 : ℝ)*(sp1) + (7140236503/25000000000000 : ℝ)*(sp2) + (2574308039934679/50000000000000 : ℝ)*(sp4) + (257430548412723/5000000000000 : ℝ)*(sp5) + (5148585794414391/100000000000000 : ℝ)*(sp6) + (614518750071523/25000000000000 : ℝ)*(sp7) + (614518750071523/25000000000000 : ℝ)*(f.failure) + (2574308039934679/50000000000000 : ℝ)*(f.sum) + (853479154817/651250000000000000000000000 : ℝ)*base65 + (68839786385678889/8140625000000000000000000000000 : ℝ)*base68 + (45737740643460139/8140625000000000000000000000000 : ℝ)*base70 + (13724632684991389/8140625000000000000000000000000 : ℝ)*base72 + (964736896321/325625000000000000000000000 : ℝ)*base73 + (104722666959491389/8140625000000000000000000000000 : ℝ)*base76 + (10507655496253507/4070312500000000000000000000000 : ℝ)*base78 + (29177001577366389/8140625000000000000000000000000 : ℝ)*base80 + (6731608203973/2605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5159783/2500000000000000000000 : ℝ)*base89 + (5159783/2500000000000000000000 : ℝ)*base91 + (5159783/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1342_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2463/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2173/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1342_s4_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-63864753/312500000 : ℝ)*x 0 + (433221/800000 : ℝ)*x 1 + (104844989/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63864753/312500000 : ℝ)^2151 ≤ (12444962955809/100000000000000 : ℝ)^1639 := by
    have hnat : (63864753 : ℕ)^2151*100000000000000^1639 ≤ 12444962955809^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63864753 312500000 12444962955809 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433221/800000 : ℝ)^2151 ≤ (22355072850569/50000000000000 : ℝ)^1639 := by
    have hnat : (433221 : ℕ)^2151*50000000000000^1639 ≤ 22355072850569^1639*800000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433221 800000 22355072850569 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104844989/200000000 : ℝ)^2151 ≤ (21422445662067/50000000000000 : ℝ)^1639 := by
    have hnat : (104844989 : ℕ)^2151*50000000000000^1639 ≤ 21422445662067^1639*200000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104844989 200000000 21422445662067 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63864753/312500000 : ℝ), (433221/800000 : ℝ), (104844989/200000000 : ℝ)] ![(12444962955809/100000000000000 : ℝ), (22355072850569/50000000000000 : ℝ), (21422445662067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63864753/312500000 : ℝ)|^2151 ≤ (12444962955809/100000000000000 : ℝ)^1639
        have hw : |(-63864753/312500000 : ℝ)|=(63864753/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(433221/800000 : ℝ)|^2151 ≤ (22355072850569/50000000000000 : ℝ)^1639
        have hw : |(433221/800000 : ℝ)|=(433221/800000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104844989/200000000 : ℝ)|^2151 ≤ (21422445662067/50000000000000 : ℝ)^1639
        have hw : |(104844989/200000000 : ℝ)|=(104844989/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s4_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349651597/10000000000 : ℝ)*x 0 + (-532967931/2500000000 : ℝ)*x 1 + (1048449861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349651597/10000000000 : ℝ)^2151 ≤ (44000569405599/100000000000000 : ℝ)^1639 := by
    have hnat : (5349651597 : ℕ)^2151*100000000000000^1639 ≤ 44000569405599^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349651597 10000000000 44000569405599 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532967931/2500000000 : ℝ)^2151 ≤ (13154540810583/100000000000000 : ℝ)^1639 := by
    have hnat : (532967931 : ℕ)^2151*100000000000000^1639 ≤ 13154540810583^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532967931 2500000000 13154540810583 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048449861/2000000000 : ℝ)^2151 ≤ (21422444884423/50000000000000 : ℝ)^1639 := by
    have hnat : (1048449861 : ℕ)^2151*50000000000000^1639 ≤ 21422444884423^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048449861 2000000000 21422444884423 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349651597/10000000000 : ℝ), (-532967931/2500000000 : ℝ), (1048449861/2000000000 : ℝ)] ![(44000569405599/100000000000000 : ℝ), (13154540810583/100000000000000 : ℝ), (21422444884423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349651597/10000000000 : ℝ)|^2151 ≤ (44000569405599/100000000000000 : ℝ)^1639
        have hw : |(5349651597/10000000000 : ℝ)|=(5349651597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532967931/2500000000 : ℝ)|^2151 ≤ (13154540810583/100000000000000 : ℝ)^1639
        have hw : |(-532967931/2500000000 : ℝ)|=(532967931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048449861/2000000000 : ℝ)|^2151 ≤ (21422444884423/50000000000000 : ℝ)^1639
        have hw : |(1048449861/2000000000 : ℝ)|=(1048449861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s4_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337412999/2500000000 : ℝ)*x 0 + (5242249033/10000000000 : ℝ)*x 1 + (-2131871553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337412999/2500000000 : ℝ)^2151 ≤ (22000286856261/50000000000000 : ℝ)^1639 := by
    have hnat : (1337412999 : ℕ)^2151*50000000000000^1639 ≤ 22000286856261^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337412999 2500000000 22000286856261 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242249033/10000000000 : ℝ)^2151 ≤ (42844886851341/100000000000000 : ℝ)^1639 := by
    have hnat : (5242249033 : ℕ)^2151*100000000000000^1639 ≤ 42844886851341^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242249033 10000000000 42844886851341 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131871553/10000000000 : ℝ)^2151 ≤ (1315453942583/10000000000000 : ℝ)^1639 := by
    have hnat : (2131871553 : ℕ)^2151*10000000000000^1639 ≤ 1315453942583^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131871553 10000000000 1315453942583 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337412999/2500000000 : ℝ), (5242249033/10000000000 : ℝ), (-2131871553/10000000000 : ℝ)] ![(22000286856261/50000000000000 : ℝ), (42844886851341/100000000000000 : ℝ), (1315453942583/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337412999/2500000000 : ℝ)|^2151 ≤ (22000286856261/50000000000000 : ℝ)^1639
        have hw : |(1337412999/2500000000 : ℝ)|=(1337412999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242249033/10000000000 : ℝ)|^2151 ≤ (42844886851341/100000000000000 : ℝ)^1639
        have hw : |(5242249033/10000000000 : ℝ)|=(5242249033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131871553/10000000000 : ℝ)|^2151 ≤ (1315453942583/10000000000000 : ℝ)^1639
        have hw : |(-2131871553/10000000000 : ℝ)|=(2131871553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s4_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081610651/2500000000 : ℝ)*x 0 + (4148793157/10000000000 : ℝ)*x 1 + (2255591133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081610651/2500000000 : ℝ)^2151 ≤ (8325369206723/25000000000000 : ℝ)^1639 := by
    have hnat : (1081610651 : ℕ)^2151*25000000000000^1639 ≤ 8325369206723^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081610651 2500000000 8325369206723 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148793157/10000000000 : ℝ)^2151 ≤ (393981711697/1250000000000 : ℝ)^1639 := by
    have hnat : (4148793157 : ℕ)^2151*1250000000000^1639 ≤ 393981711697^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148793157 10000000000 393981711697 1250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255591133/5000000000 : ℝ)^2151 ≤ (35179986230541/100000000000000 : ℝ)^1639 := by
    have hnat : (2255591133 : ℕ)^2151*100000000000000^1639 ≤ 35179986230541^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255591133 5000000000 35179986230541 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081610651/2500000000 : ℝ), (4148793157/10000000000 : ℝ), (2255591133/5000000000 : ℝ)] ![(8325369206723/25000000000000 : ℝ), (393981711697/1250000000000 : ℝ), (35179986230541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081610651/2500000000 : ℝ)|^2151 ≤ (8325369206723/25000000000000 : ℝ)^1639
        have hw : |(1081610651/2500000000 : ℝ)|=(1081610651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148793157/10000000000 : ℝ)|^2151 ≤ (393981711697/1250000000000 : ℝ)^1639
        have hw : |(4148793157/10000000000 : ℝ)|=(4148793157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255591133/5000000000 : ℝ)|^2151 ≤ (35179986230541/100000000000000 : ℝ)^1639
        have hw : |(2255591133/5000000000 : ℝ)|=(2255591133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s4_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-20436857/100000000 : ℝ)*x 0 + (2621443273/5000000000 : ℝ)*x 1 + (338413861/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20436857/100000000 : ℝ)^2151 ≤ (622253583809/5000000000000 : ℝ)^1639 := by
    have hnat : (20436857 : ℕ)^2151*5000000000000^1639 ≤ 622253583809^1639*100000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20436857 100000000 622253583809 5000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621443273/5000000000 : ℝ)^2151 ≤ (21425862512321/50000000000000 : ℝ)^1639 := by
    have hnat : (2621443273 : ℕ)^2151*50000000000000^1639 ≤ 21425862512321^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621443273 5000000000 21425862512321 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338413861/625000000 : ℝ)^2151 ≤ (2793950204961/6250000000000 : ℝ)^1639 := by
    have hnat : (338413861 : ℕ)^2151*6250000000000^1639 ≤ 2793950204961^1639*625000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338413861 625000000 2793950204961 6250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20436857/100000000 : ℝ), (2621443273/5000000000 : ℝ), (338413861/625000000 : ℝ)] ![(622253583809/5000000000000 : ℝ), (21425862512321/50000000000000 : ℝ), (2793950204961/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20436857/100000000 : ℝ)|^2151 ≤ (622253583809/5000000000000 : ℝ)^1639
        have hw : |(-20436857/100000000 : ℝ)|=(20436857/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621443273/5000000000 : ℝ)|^2151 ≤ (21425862512321/50000000000000 : ℝ)^1639
        have hw : |(2621443273/5000000000 : ℝ)|=(2621443273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338413861/625000000 : ℝ)|^2151 ≤ (2793950204961/6250000000000 : ℝ)^1639
        have hw : |(338413861/625000000 : ℝ)|=(338413861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s4_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061017473/2000000000 : ℝ)*x 0 + (-195949939/1000000000 : ℝ)*x 1 + (5414621579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061017473/2000000000 : ℝ)^2151 ≤ (21760078533099/50000000000000 : ℝ)^1639 := by
    have hnat : (1061017473 : ℕ)^2151*50000000000000^1639 ≤ 21760078533099^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061017473 2000000000 21760078533099 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195949939/1000000000 : ℝ)^2151 ≤ (2944160441677/25000000000000 : ℝ)^1639 := by
    have hnat : (195949939 : ℕ)^2151*25000000000000^1639 ≤ 2944160441677^1639*1000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195949939 1000000000 2944160441677 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414621579/10000000000 : ℝ)^2151 ≤ (22351600572433/50000000000000 : ℝ)^1639 := by
    have hnat : (5414621579 : ℕ)^2151*50000000000000^1639 ≤ 22351600572433^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414621579 10000000000 22351600572433 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061017473/2000000000 : ℝ), (-195949939/1000000000 : ℝ), (5414621579/10000000000 : ℝ)] ![(21760078533099/50000000000000 : ℝ), (2944160441677/25000000000000 : ℝ), (22351600572433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061017473/2000000000 : ℝ)|^2151 ≤ (21760078533099/50000000000000 : ℝ)^1639
        have hw : |(1061017473/2000000000 : ℝ)|=(1061017473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195949939/1000000000 : ℝ)|^2151 ≤ (2944160441677/25000000000000 : ℝ)^1639
        have hw : |(-195949939/1000000000 : ℝ)|=(195949939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414621579/10000000000 : ℝ)|^2151 ≤ (22351600572433/50000000000000 : ℝ)^1639
        have hw : |(5414621579/10000000000 : ℝ)|=(5414621579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s4_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305087183/10000000000 : ℝ)*x 0 + (676827709/1250000000 : ℝ)*x 1 + (-1959499511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305087183/10000000000 : ℝ)^2151 ≤ (10880038776691/25000000000000 : ℝ)^1639 := by
    have hnat : (5305087183 : ℕ)^2151*25000000000000^1639 ≤ 10880038776691^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305087183 10000000000 10880038776691 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676827709/1250000000 : ℝ)^2151 ≤ (2793950134533/6250000000000 : ℝ)^1639 := by
    have hnat : (676827709 : ℕ)^2151*6250000000000^1639 ≤ 2793950134533^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676827709 1250000000 2793950134533 6250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1959499511/10000000000 : ℝ)^2151 ≤ (2944160680273/25000000000000 : ℝ)^1639 := by
    have hnat : (1959499511 : ℕ)^2151*25000000000000^1639 ≤ 2944160680273^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959499511 10000000000 2944160680273 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305087183/10000000000 : ℝ), (676827709/1250000000 : ℝ), (-1959499511/10000000000 : ℝ)] ![(10880038776691/25000000000000 : ℝ), (2793950134533/6250000000000 : ℝ), (2944160680273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305087183/10000000000 : ℝ)|^2151 ≤ (10880038776691/25000000000000 : ℝ)^1639
        have hw : |(5305087183/10000000000 : ℝ)|=(5305087183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676827709/1250000000 : ℝ)|^2151 ≤ (2793950134533/6250000000000 : ℝ)^1639
        have hw : |(676827709/1250000000 : ℝ)|=(676827709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1959499511/10000000000 : ℝ)|^2151 ≤ (2944160680273/25000000000000 : ℝ)^1639
        have hw : |(-1959499511/10000000000 : ℝ)|=(1959499511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s4_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163235049/5000000000 : ℝ)*x 0 + (1127461791/2500000000 : ℝ)*x 1 + (4150135657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163235049/5000000000 : ℝ)^2151 ≤ (33301754563011/100000000000000 : ℝ)^1639 := by
    have hnat : (2163235049 : ℕ)^2151*100000000000000^1639 ≤ 33301754563011^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163235049 5000000000 33301754563011 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127461791/2500000000 : ℝ)^2151 ≤ (35166322757109/100000000000000 : ℝ)^1639 := by
    have hnat : (1127461791 : ℕ)^2151*100000000000000^1639 ≤ 35166322757109^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127461791 2500000000 35166322757109 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4150135657/10000000000 : ℝ)^2151 ≤ (31531922662833/100000000000000 : ℝ)^1639 := by
    have hnat : (4150135657 : ℕ)^2151*100000000000000^1639 ≤ 31531922662833^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150135657 10000000000 31531922662833 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163235049/5000000000 : ℝ), (1127461791/2500000000 : ℝ), (4150135657/10000000000 : ℝ)] ![(33301754563011/100000000000000 : ℝ), (35166322757109/100000000000000 : ℝ), (31531922662833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163235049/5000000000 : ℝ)|^2151 ≤ (33301754563011/100000000000000 : ℝ)^1639
        have hw : |(2163235049/5000000000 : ℝ)|=(2163235049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127461791/2500000000 : ℝ)|^2151 ≤ (35166322757109/100000000000000 : ℝ)^1639
        have hw : |(1127461791/2500000000 : ℝ)|=(1127461791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4150135657/10000000000 : ℝ)|^2151 ≤ (31531922662833/100000000000000 : ℝ)^1639
        have hw : |(4150135657/10000000000 : ℝ)|=(4150135657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2173/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5549/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2173/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2173/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2173/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2173/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2173/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2173/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2173/20000 : ℝ) ^ (4301/1024 : ℝ) ≤ (8935864883336661/100000000000000000000 : ℝ) := by
    have hpowers : (2173/20000 : ℝ)^4301 ≤ (8935864883336661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2173 : ℕ)^4301*100000000000000000000^1024 ≤ 8935864883336661^1024*20000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2173 20000 8935864883336661 100000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2173/20000 : ℝ)) (X := (8935864883336661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15009/100000 : ℝ) ^ (4301/1024 : ℝ) ≤ (17357473763323059/50000000000000000000 : ℝ) := by
    have hpowers : (15009/100000 : ℝ)^4301 ≤ (17357473763323059/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15009 : ℕ)^4301*50000000000000000000^1024 ≤ 17357473763323059^1024*100000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15009 100000 17357473763323059 50000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15009/100000 : ℝ)) (X := (17357473763323059/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008935864883336661/50000000000000000000 : ℝ) ≤ (5000212734311027/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (50008935864883336661/50000000000000000000 : ℝ)^1024 ≤ (5000212734311027/5000000000000000 : ℝ)^4301 := by
      have hnat : (50008935864883336661 : ℕ)^1024*5000000000000000^4301 ≤ 5000212734311027^4301*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008935864883336661 50000000000000000000 5000212734311027 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000212734311027/5000000000000000 : ℝ)) (X := (50008935864883336661/50000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043650812409982779/100000000000000000000 : ℝ) ≤ (5000519541976933/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (100043650812409982779/100000000000000000000 : ℝ)^1024 ≤ (5000519541976933/5000000000000000 : ℝ)^4301 := by
      have hnat : (100043650812409982779 : ℕ)^1024*5000000000000000^4301 ≤ 5000519541976933^4301*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043650812409982779 100000000000000000000 5000519541976933 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000519541976933/5000000000000000 : ℝ)) (X := (100043650812409982779/100000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017357473763323059/25000000000000000000 : ℝ) ≤ (5000826349642839/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (25017357473763323059/25000000000000000000 : ℝ)^1024 ≤ (5000826349642839/5000000000000000 : ℝ)^4301 := by
      have hnat : (25017357473763323059 : ℕ)^1024*5000000000000000^4301 ≤ 5000826349642839^4301*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017357473763323059 25000000000000000000 5000826349642839 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000826349642839/5000000000000000 : ℝ)) (X := (25017357473763323059/25000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8935864883336661/100000000000000000000 : ℝ) ≤ ((739793380014455661/740000000000000000 : ℝ)+2*(21914833279/14800000000000 : ℝ)*(2173/20000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (739793380014455661/740000000000000000 : ℝ)+2*(21914833279/14800000000000 : ℝ)*(2173/20000 : ℝ)=(5000212734311027/5000000000000000 : ℝ) by norm_num, show 1+2*(8935864883336661/100000000000000000000 : ℝ)=(50008935864883336661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17357473763323059/50000000000000000000 : ℝ)+(8935864883336661/100000000000000000000 : ℝ) ≤ ((739793380014455661/740000000000000000 : ℝ)+(21914833279/14800000000000 : ℝ)*((15009/100000 : ℝ)+(2173/20000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (739793380014455661/740000000000000000 : ℝ)+(21914833279/14800000000000 : ℝ)*((15009/100000 : ℝ)+(2173/20000 : ℝ))=(5000519541976933/5000000000000000 : ℝ) by norm_num, show 1+(17357473763323059/50000000000000000000 : ℝ)+(8935864883336661/100000000000000000000 : ℝ)=(100043650812409982779/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17357473763323059/50000000000000000000 : ℝ) ≤ ((739793380014455661/740000000000000000 : ℝ)+2*(21914833279/14800000000000 : ℝ)*(15009/100000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (739793380014455661/740000000000000000 : ℝ)+2*(21914833279/14800000000000 : ℝ)*(15009/100000 : ℝ)=(5000826349642839/5000000000000000 : ℝ) by norm_num, show 1+2*(17357473763323059/50000000000000000000 : ℝ)=(25017357473763323059/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (739793380014455661/740000000000000000 : ℝ)*(X 1 0+X 2 0)+(21914833279/14800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2173/20000 : ℝ)) (hi := (15009/100000 : ℝ)) (c := (739793380014455661/740000000000000000 : ℝ)) (alpha := (21914833279/14800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (739793380014455661/740000000000000000 : ℝ)*(X 0 1+X 2 1)+(21914833279/14800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2173/20000 : ℝ)) (hi := (15009/100000 : ℝ)) (c := (739793380014455661/740000000000000000 : ℝ)) (alpha := (21914833279/14800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (739793380014455661/740000000000000000 : ℝ)*(X 0 2+X 1 2)+(21914833279/14800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2173/20000 : ℝ)) (hi := (15009/100000 : ℝ)) (c := (739793380014455661/740000000000000000 : ℝ)) (alpha := (21914833279/14800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-63864753/312500000 : ℝ)*X 0 0+(433221/800000 : ℝ)*X 0 1+(104844989/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349651597/10000000000 : ℝ)*X 1 0+(-532967931/2500000000 : ℝ)*X 1 1+(1048449861/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337412999/2500000000 : ℝ)*X 2 0+(5242249033/10000000000 : ℝ)*X 2 1+(-2131871553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081610651/2500000000 : ℝ)*X 0 0+(4148793157/10000000000 : ℝ)*X 0 1+(2255591133/5000000000 : ℝ)*X 0 2+(1081610651/2500000000 : ℝ)*X 1 0+(4148793157/10000000000 : ℝ)*X 1 1+(2255591133/5000000000 : ℝ)*X 1 2+(1081610651/2500000000 : ℝ)*X 2 0+(4148793157/10000000000 : ℝ)*X 2 1+(2255591133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-20436857/100000000 : ℝ)*X 0 0+(2621443273/5000000000 : ℝ)*X 0 1+(338413861/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061017473/2000000000 : ℝ)*X 1 0+(-195949939/1000000000 : ℝ)*X 1 1+(5414621579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305087183/10000000000 : ℝ)*X 2 0+(676827709/1250000000 : ℝ)*X 2 1+(-1959499511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163235049/5000000000 : ℝ)*X 0 0+(1127461791/2500000000 : ℝ)*X 0 1+(4150135657/10000000000 : ℝ)*X 0 2+(2163235049/5000000000 : ℝ)*X 1 0+(1127461791/2500000000 : ℝ)*X 1 1+(4150135657/10000000000 : ℝ)*X 1 2+(2163235049/5000000000 : ℝ)*X 2 0+(1127461791/2500000000 : ℝ)*X 2 1+(4150135657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43176769060682232453471819/4625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2273076413/100000000000000 : ℝ)*(base19) + (507974097/25000000000000 : ℝ)*(base23) + (89911121/25000000000000 : ℝ)*(lower2) + (274197167/100000000000000 : ℝ)*(upper3) + (55978239/100000000000000 : ℝ)*(upper5) + (1067437595167107/25000000000000 : ℝ)*(major0) + (1067437595167107/25000000000000 : ℝ)*(major1) + (1067437595167107/25000000000000 : ℝ)*(major2) + (5779949376527343/100000000000000 : ℝ)*(sp0) + (722498634322007/12500000000000 : ℝ)*(sp1) + (2889994657878041/50000000000000 : ℝ)*(sp2) + (1379741601991701/50000000000000 : ℝ)*(sp3) + (41971125127/100000000000000 : ℝ)*(sp4) + (25898517051/100000000000000 : ℝ)*(sp7) + (2759509102500453/100000000000000 : ℝ)*(f.failure) + (5779991347652469/100000000000000 : ℝ)*(f.sum) + (630285317077/185000000000000000000000000 : ℝ)*base66 + (75352129290207273/18500000000000000000000000000000 : ℝ)*base68 + (238895141821292727/18500000000000000000000000000000 : ℝ)*base69 + (376817305726792727/18500000000000000000000000000000 : ℝ)*base71 + (1214466838937/185000000000000000000000000 : ℝ)*base74 + (236879304528292727/18500000000000000000000000000000 : ℝ)*base75 + (224338858286792727/18500000000000000000000000000000 : ℝ)*base77 + (55535558225792727/18500000000000000000000000000000 : ℝ)*base79 + (31466454739/5781250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (55434687/10000000000000000000000 : ℝ)*base90 + (55434687/10000000000000000000000 : ℝ)*base92 + (55434687/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (336721785732836345100284877/37000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (459773189/25000000000000 : ℝ)*(base19) + (1755385961/100000000000000 : ℝ)*(base23) + (10282193/6250000000000 : ℝ)*(upper3) + (82072069/100000000000000 : ℝ)*(lower4) + (16062887/6250000000000 : ℝ)*(upper5) + (4301460008793419/100000000000000 : ℝ)*(major0) + (4301460008793419/100000000000000 : ℝ)*(major1) + (4301460008793419/100000000000000 : ℝ)*(major2) + (16361885247/50000000000000 : ℝ)*(sp1) + (28122808373/100000000000000 : ℝ)*(sp2) + (5822916906095733/100000000000000 : ℝ)*(sp4) + (2911441171616241/50000000000000 : ℝ)*(sp5) + (5822887027901399/100000000000000 : ℝ)*(sp6) + (139000140406907/5000000000000 : ℝ)*(sp7) + (139000140406907/5000000000000 : ℝ)*(f.failure) + (5822916906095733/100000000000000 : ℝ)*(f.sum) + (784825127899/740000000000000000000000000 : ℝ)*base66 + (27351730942855041/74000000000000000000000000000000 : ℝ)*base68 + (166478880082855041/74000000000000000000000000000000 : ℝ)*base70 + (413185021802855041/74000000000000000000000000000000 : ℝ)*base72 + (1089063771141/740000000000000000000000000 : ℝ)*base73 + (739321528357144959/74000000000000000000000000000000 : ℝ)*base75 + (3933540099144959/74000000000000000000000000000000 : ℝ)*base77 + (647054683148855041/74000000000000000000000000000000 : ℝ)*base80 + (969116062621/740000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3985247/500000000000000000000 : ℝ)*base89 + (3985247/500000000000000000000 : ℝ)*base91 + (3985247/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1342_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2173/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1342_s5_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-51098091/250000000 : ℝ)*x 0 + (169159263/312500000 : ℝ)*x 1 + (5244249939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51098091/250000000 : ℝ)^2151 ≤ (12446973280291/100000000000000 : ℝ)^1639 := by
    have hnat : (51098091 : ℕ)^2151*100000000000000^1639 ≤ 12446973280291^1639*250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51098091 250000000 12446973280291 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169159263/312500000 : ℝ)^2151 ≤ (22343338307301/50000000000000 : ℝ)^1639 := by
    have hnat : (169159263 : ℕ)^2151*50000000000000^1639 ≤ 22343338307301^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169159263 312500000 22343338307301 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244249939/10000000000 : ℝ)^2151 ≤ (42866350096371/100000000000000 : ℝ)^1639 := by
    have hnat : (5244249939 : ℕ)^2151*100000000000000^1639 ≤ 42866350096371^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244249939 10000000000 42866350096371 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51098091/250000000 : ℝ), (169159263/312500000 : ℝ), (5244249939/10000000000 : ℝ)] ![(12446973280291/100000000000000 : ℝ), (22343338307301/50000000000000 : ℝ), (42866350096371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51098091/250000000 : ℝ)|^2151 ≤ (12446973280291/100000000000000 : ℝ)^1639
        have hw : |(-51098091/250000000 : ℝ)|=(51098091/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169159263/312500000 : ℝ)|^2151 ≤ (22343338307301/50000000000000 : ℝ)^1639
        have hw : |(169159263/312500000 : ℝ)|=(169159263/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244249939/10000000000 : ℝ)|^2151 ≤ (42866350096371/100000000000000 : ℝ)^1639
        have hw : |(5244249939/10000000000 : ℝ)|=(5244249939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s5_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337274509/2500000000 : ℝ)*x 0 + (-425991847/2000000000 : ℝ)*x 1 + (5244249937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337274509/2500000000 : ℝ)^2151 ≤ (4399459420183/10000000000000 : ℝ)^1639 := by
    have hnat : (1337274509 : ℕ)^2151*10000000000000^1639 ≤ 4399459420183^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337274509 2500000000 4399459420183 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425991847/2000000000 : ℝ)^2151 ≤ (13139055705529/100000000000000 : ℝ)^1639 := by
    have hnat : (425991847 : ℕ)^2151*100000000000000^1639 ≤ 13139055705529^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425991847 2000000000 13139055705529 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244249937/10000000000 : ℝ)^2151 ≤ (10716587518729/25000000000000 : ℝ)^1639 := by
    have hnat : (5244249937 : ℕ)^2151*25000000000000^1639 ≤ 10716587518729^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244249937 10000000000 10716587518729 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337274509/2500000000 : ℝ), (-425991847/2000000000 : ℝ), (5244249937/10000000000 : ℝ)] ![(4399459420183/10000000000000 : ℝ), (13139055705529/100000000000000 : ℝ), (10716587518729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337274509/2500000000 : ℝ)|^2151 ≤ (4399459420183/10000000000000 : ℝ)^1639
        have hw : |(1337274509/2500000000 : ℝ)|=(1337274509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425991847/2000000000 : ℝ)|^2151 ≤ (13139055705529/100000000000000 : ℝ)^1639
        have hw : |(-425991847/2000000000 : ℝ)|=(425991847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244249937/10000000000 : ℝ)|^2151 ≤ (10716587518729/25000000000000 : ℝ)^1639
        have hw : |(5244249937/10000000000 : ℝ)|=(5244249937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s5_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349098047/10000000000 : ℝ)*x 0 + (5244249947/10000000000 : ℝ)*x 1 + (-2129959207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349098047/10000000000 : ℝ)^2151 ≤ (10998648580141/25000000000000 : ℝ)^1639 := by
    have hnat : (5349098047 : ℕ)^2151*25000000000000^1639 ≤ 10998648580141^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349098047 10000000000 10998648580141 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244249947/10000000000 : ℝ)^2151 ≤ (4286635018219/10000000000000 : ℝ)^1639 := by
    have hnat : (5244249947 : ℕ)^2151*10000000000000^1639 ≤ 4286635018219^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244249947 10000000000 4286635018219 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129959207/10000000000 : ℝ)^2151 ≤ (13139055478849/100000000000000 : ℝ)^1639 := by
    have hnat : (2129959207 : ℕ)^2151*100000000000000^1639 ≤ 13139055478849^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129959207 10000000000 13139055478849 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349098047/10000000000 : ℝ), (5244249947/10000000000 : ℝ), (-2129959207/10000000000 : ℝ)] ![(10998648580141/25000000000000 : ℝ), (4286635018219/10000000000000 : ℝ), (13139055478849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349098047/10000000000 : ℝ)|^2151 ≤ (10998648580141/25000000000000 : ℝ)^1639
        have hw : |(5349098047/10000000000 : ℝ)|=(5349098047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244249947/10000000000 : ℝ)|^2151 ≤ (4286635018219/10000000000000 : ℝ)^1639
        have hw : |(5244249947/10000000000 : ℝ)|=(5244249947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2129959207/10000000000 : ℝ)|^2151 ≤ (13139055478849/100000000000000 : ℝ)^1639
        have hw : |(-2129959207/10000000000 : ℝ)|=(2129959207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s5_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081648049/2500000000 : ℝ)*x 0 + (4153138743/10000000000 : ℝ)*x 1 + (36054399/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081648049/2500000000 : ℝ)^2151 ≤ (33302987966949/100000000000000 : ℝ)^1639 := by
    have hnat : (1081648049 : ℕ)^2151*100000000000000^1639 ≤ 33302987966949^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081648049 2500000000 33302987966949 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153138743/10000000000 : ℝ)^2151 ≤ (15780935284383/50000000000000 : ℝ)^1639 := by
    have hnat : (4153138743 : ℕ)^2151*50000000000000^1639 ≤ 15780935284383^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153138743 10000000000 15780935284383 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36054399/80000000 : ℝ)^2151 ≤ (35135141444747/100000000000000 : ℝ)^1639 := by
    have hnat : (36054399 : ℕ)^2151*100000000000000^1639 ≤ 35135141444747^1639*80000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36054399 80000000 35135141444747 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081648049/2500000000 : ℝ), (4153138743/10000000000 : ℝ), (36054399/80000000 : ℝ)] ![(33302987966949/100000000000000 : ℝ), (15780935284383/50000000000000 : ℝ), (35135141444747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081648049/2500000000 : ℝ)|^2151 ≤ (33302987966949/100000000000000 : ℝ)^1639
        have hw : |(1081648049/2500000000 : ℝ)|=(1081648049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153138743/10000000000 : ℝ)|^2151 ≤ (15780935284383/50000000000000 : ℝ)^1639
        have hw : |(4153138743/10000000000 : ℝ)|=(4153138743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36054399/80000000 : ℝ)|^2151 ≤ (35135141444747/100000000000000 : ℝ)^1639
        have hw : |(36054399/80000000 : ℝ)|=(36054399/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s5_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043935969/10000000000 : ℝ)*x 0 + (2622428557/5000000000 : ℝ)*x 1 + (1082497221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043935969/10000000000 : ℝ)^2151 ≤ (12447071814903/100000000000000 : ℝ)^1639 := by
    have hnat : (2043935969 : ℕ)^2151*100000000000000^1639 ≤ 12447071814903^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043935969 10000000000 12447071814903 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622428557/5000000000 : ℝ)^2151 ≤ (10718215906213/25000000000000 : ℝ)^1639 := by
    have hnat : (2622428557 : ℕ)^2151*25000000000000^1639 ≤ 10718215906213^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622428557 5000000000 10718215906213 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082497221/2000000000 : ℝ)^2151 ≤ (44680064546767/100000000000000 : ℝ)^1639 := by
    have hnat : (1082497221 : ℕ)^2151*100000000000000^1639 ≤ 44680064546767^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082497221 2000000000 44680064546767 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043935969/10000000000 : ℝ), (2622428557/5000000000 : ℝ), (1082497221/2000000000 : ℝ)] ![(12447071814903/100000000000000 : ℝ), (10718215906213/25000000000000 : ℝ), (44680064546767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043935969/10000000000 : ℝ)|^2151 ≤ (12447071814903/100000000000000 : ℝ)^1639
        have hw : |(-2043935969/10000000000 : ℝ)|=(2043935969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622428557/5000000000 : ℝ)|^2151 ≤ (10718215906213/25000000000000 : ℝ)^1639
        have hw : |(2622428557/5000000000 : ℝ)|=(2622428557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082497221/2000000000 : ℝ)|^2151 ≤ (44680064546767/100000000000000 : ℝ)^1639
        have hw : |(1082497221/2000000000 : ℝ)|=(1082497221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s5_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652803499/5000000000 : ℝ)*x 0 + (-1961723033/10000000000 : ℝ)*x 1 + (541248611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652803499/5000000000 : ℝ)^2151 ≤ (43525751585009/100000000000000 : ℝ)^1639 := by
    have hnat : (2652803499 : ℕ)^2151*100000000000000^1639 ≤ 43525751585009^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652803499 5000000000 43525751585009 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1961723033/10000000000 : ℝ)^2151 ≤ (2358836758969/20000000000000 : ℝ)^1639 := by
    have hnat : (1961723033 : ℕ)^2151*20000000000000^1639 ≤ 2358836758969^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961723033 10000000000 2358836758969 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541248611/1000000000 : ℝ)^2151 ≤ (5585008075117/12500000000000 : ℝ)^1639 := by
    have hnat : (541248611 : ℕ)^2151*12500000000000^1639 ≤ 5585008075117^1639*1000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541248611 1000000000 5585008075117 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652803499/5000000000 : ℝ), (-1961723033/10000000000 : ℝ), (541248611/1000000000 : ℝ)] ![(43525751585009/100000000000000 : ℝ), (2358836758969/20000000000000 : ℝ), (5585008075117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652803499/5000000000 : ℝ)|^2151 ≤ (43525751585009/100000000000000 : ℝ)^1639
        have hw : |(2652803499/5000000000 : ℝ)|=(2652803499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1961723033/10000000000 : ℝ)|^2151 ≤ (2358836758969/20000000000000 : ℝ)^1639
        have hw : |(-1961723033/10000000000 : ℝ)|=(1961723033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541248611/1000000000 : ℝ)|^2151 ≤ (5585008075117/12500000000000 : ℝ)^1639
        have hw : |(541248611/1000000000 : ℝ)|=(541248611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s5_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305606983/10000000000 : ℝ)*x 0 + (5412486123/10000000000 : ℝ)*x 1 + (-490430759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305606983/10000000000 : ℝ)^2151 ≤ (5440718927939/12500000000000 : ℝ)^1639 := by
    have hnat : (5305606983 : ℕ)^2151*12500000000000^1639 ≤ 5440718927939^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305606983 10000000000 5440718927939 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412486123/10000000000 : ℝ)^2151 ≤ (1787202589671/4000000000000 : ℝ)^1639 := by
    have hnat : (5412486123 : ℕ)^2151*4000000000000^1639 ≤ 1787202589671^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412486123 10000000000 1787202589671 4000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490430759/2500000000 : ℝ)^2151 ≤ (2948545954629/25000000000000 : ℝ)^1639 := by
    have hnat : (490430759 : ℕ)^2151*25000000000000^1639 ≤ 2948545954629^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490430759 2500000000 2948545954629 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305606983/10000000000 : ℝ), (5412486123/10000000000 : ℝ), (-490430759/2500000000 : ℝ)] ![(5440718927939/12500000000000 : ℝ), (1787202589671/4000000000000 : ℝ), (2948545954629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305606983/10000000000 : ℝ)|^2151 ≤ (5440718927939/12500000000000 : ℝ)^1639
        have hw : |(5305606983/10000000000 : ℝ)|=(5305606983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412486123/10000000000 : ℝ)|^2151 ≤ (1787202589671/4000000000000 : ℝ)^1639
        have hw : |(5412486123/10000000000 : ℝ)|=(5412486123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490430759/2500000000 : ℝ)|^2151 ≤ (2948545954629/25000000000000 : ℝ)^1639
        have hw : |(-490430759/2500000000 : ℝ)|=(490430759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s5_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163308991/5000000000 : ℝ)*x 0 + (901105637/2000000000 : ℝ)*x 1 + (103860427/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163308991/5000000000 : ℝ)^2151 ≤ (33303248452163/100000000000000 : ℝ)^1639 := by
    have hnat : (2163308991 : ℕ)^2151*100000000000000^1639 ≤ 33303248452163^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163308991 5000000000 33303248452163 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901105637/2000000000 : ℝ)^2151 ≤ (35122130854387/100000000000000 : ℝ)^1639 := by
    have hnat : (901105637 : ℕ)^2151*100000000000000^1639 ≤ 35122130854387^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901105637 2000000000 35122130854387 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103860427/250000000 : ℝ)^2151 ≤ (3946827585053/12500000000000 : ℝ)^1639 := by
    have hnat : (103860427 : ℕ)^2151*12500000000000^1639 ≤ 3946827585053^1639*250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103860427 250000000 3946827585053 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163308991/5000000000 : ℝ), (901105637/2000000000 : ℝ), (103860427/250000000 : ℝ)] ![(33303248452163/100000000000000 : ℝ), (35122130854387/100000000000000 : ℝ), (3946827585053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163308991/5000000000 : ℝ)|^2151 ≤ (33303248452163/100000000000000 : ℝ)^1639
        have hw : |(2163308991/5000000000 : ℝ)|=(2163308991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901105637/2000000000 : ℝ)|^2151 ≤ (35122130854387/100000000000000 : ℝ)^1639
        have hw : |(901105637/2000000000 : ℝ)|=(901105637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103860427/250000000 : ℝ)|^2151 ≤ (3946827585053/12500000000000 : ℝ)^1639
        have hw : |(103860427/250000000 : ℝ)|=(103860427/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11141/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2943/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5549/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5549/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5549/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5549/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5549/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5549/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5549/50000 : ℝ) ^ (4301/1024 : ℝ) ≤ (488440148607431/5000000000000000000 : ℝ) := by
    have hpowers : (5549/50000 : ℝ)^4301 ≤ (488440148607431/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5549 : ℕ)^4301*5000000000000000000^1024 ≤ 488440148607431^1024*50000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5549 50000 488440148607431 5000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5549/50000 : ℝ)) (X := (488440148607431/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (4301/1024 : ℝ) ≤ (161843029485487/500000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^4301 ≤ (161843029485487/500000000000000000 : ℝ)^1024 := by
      have hnat : (14761 : ℕ)^4301*500000000000000000^1024 ≤ 161843029485487^1024*100000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 161843029485487 500000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (161843029485487/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500488440148607431/2500000000000000000 : ℝ) ≤ (500023256242237/500000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (2500488440148607431/2500000000000000000 : ℝ)^1024 ≤ (500023256242237/500000000000000 : ℝ)^4301 := by
      have hnat : (2500488440148607431 : ℕ)^1024*500000000000000^4301 ≤ 500023256242237^4301*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500488440148607431 2500000000000000000 500023256242237 500000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500023256242237/500000000000000 : ℝ)) (X := (2500488440148607431/2500000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002106870443462301/5000000000000000000 : ℝ) ≤ (10001003063983151/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (5002106870443462301/5000000000000000000 : ℝ)^1024 ≤ (10001003063983151/10000000000000000 : ℝ)^4301 := by
      have hnat : (5002106870443462301 : ℕ)^1024*10000000000000000^4301 ≤ 10001003063983151^4301*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002106870443462301 5000000000000000000 10001003063983151 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001003063983151/10000000000000000 : ℝ)) (X := (5002106870443462301/5000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (250161843029485487/250000000000000000 : ℝ) ≤ (5000770501560781/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (250161843029485487/250000000000000000 : ℝ)^1024 ≤ (5000770501560781/5000000000000000 : ℝ)^4301 := by
      have hnat : (250161843029485487 : ℕ)^1024*5000000000000000^4301 ≤ 5000770501560781^4301*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250161843029485487 250000000000000000 5000770501560781 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000770501560781/5000000000000000 : ℝ)) (X := (250161843029485487/250000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(488440148607431/5000000000000000000 : ℝ) ≤ ((63575978568038389/63593750000000000 : ℝ)+2*(59771015379/40700000000000 : ℝ)*(5549/50000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (63575978568038389/63593750000000000 : ℝ)+2*(59771015379/40700000000000 : ℝ)*(5549/50000 : ℝ)=(500023256242237/500000000000000 : ℝ) by norm_num, show 1+2*(488440148607431/5000000000000000000 : ℝ)=(2500488440148607431/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(161843029485487/500000000000000000 : ℝ)+(488440148607431/5000000000000000000 : ℝ) ≤ ((63575978568038389/63593750000000000 : ℝ)+(59771015379/40700000000000 : ℝ)*((14761/100000 : ℝ)+(5549/50000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (63575978568038389/63593750000000000 : ℝ)+(59771015379/40700000000000 : ℝ)*((14761/100000 : ℝ)+(5549/50000 : ℝ))=(10001003063983151/10000000000000000 : ℝ) by norm_num, show 1+(161843029485487/500000000000000000 : ℝ)+(488440148607431/5000000000000000000 : ℝ)=(5002106870443462301/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(161843029485487/500000000000000000 : ℝ) ≤ ((63575978568038389/63593750000000000 : ℝ)+2*(59771015379/40700000000000 : ℝ)*(14761/100000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (63575978568038389/63593750000000000 : ℝ)+2*(59771015379/40700000000000 : ℝ)*(14761/100000 : ℝ)=(5000770501560781/5000000000000000 : ℝ) by norm_num, show 1+2*(161843029485487/500000000000000000 : ℝ)=(250161843029485487/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63575978568038389/63593750000000000 : ℝ)*(X 1 0+X 2 0)+(59771015379/40700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (63575978568038389/63593750000000000 : ℝ)) (alpha := (59771015379/40700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63575978568038389/63593750000000000 : ℝ)*(X 0 1+X 2 1)+(59771015379/40700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (63575978568038389/63593750000000000 : ℝ)) (alpha := (59771015379/40700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63575978568038389/63593750000000000 : ℝ)*(X 0 2+X 1 2)+(59771015379/40700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (63575978568038389/63593750000000000 : ℝ)) (alpha := (59771015379/40700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51098091/250000000 : ℝ)*X 0 0+(169159263/312500000 : ℝ)*X 0 1+(5244249939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337274509/2500000000 : ℝ)*X 1 0+(-425991847/2000000000 : ℝ)*X 1 1+(5244249937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349098047/10000000000 : ℝ)*X 2 0+(5244249947/10000000000 : ℝ)*X 2 1+(-2129959207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081648049/2500000000 : ℝ)*X 0 0+(4153138743/10000000000 : ℝ)*X 0 1+(36054399/80000000 : ℝ)*X 0 2+(1081648049/2500000000 : ℝ)*X 1 0+(4153138743/10000000000 : ℝ)*X 1 1+(36054399/80000000 : ℝ)*X 1 2+(1081648049/2500000000 : ℝ)*X 2 0+(4153138743/10000000000 : ℝ)*X 2 1+(36054399/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2043935969/10000000000 : ℝ)*X 0 0+(2622428557/5000000000 : ℝ)*X 0 1+(1082497221/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652803499/5000000000 : ℝ)*X 1 0+(-1961723033/10000000000 : ℝ)*X 1 1+(541248611/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305606983/10000000000 : ℝ)*X 2 0+(5412486123/10000000000 : ℝ)*X 2 1+(-490430759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163308991/5000000000 : ℝ)*X 0 0+(901105637/2000000000 : ℝ)*X 0 1+(103860427/250000000 : ℝ)*X 0 2+(2163308991/5000000000 : ℝ)*X 1 0+(901105637/2000000000 : ℝ)*X 1 1+(103860427/250000000 : ℝ)*X 1 2+(2163308991/5000000000 : ℝ)*X 2 0+(901105637/2000000000 : ℝ)*X 2 1+(103860427/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1277708251793045469688737/171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1434760187/100000000000000 : ℝ)*(base19) + (680260189/50000000000000 : ℝ)*(base23) + (2311323/5000000000000 : ℝ)*(lower2) + (182820507/100000000000000 : ℝ)*(upper3) + (19408821/12500000000000 : ℝ)*(upper5) + (546887028369723/12500000000000 : ℝ)*(major0) + (546887028369723/12500000000000 : ℝ)*(major1) + (546887028369723/12500000000000 : ℝ)*(major2) + (5922569216441993/100000000000000 : ℝ)*(sp0) + (370162337662823/6250000000000 : ℝ)*(sp1) + (5922597476844977/100000000000000 : ℝ)*(sp2) + (1413789480039437/50000000000000 : ℝ)*(sp3) + (14810461681/50000000000000 : ℝ)*(sp4) + (2881734673/20000000000000 : ℝ)*(sp7) + (1413796684376119/50000000000000 : ℝ)*(f.failure) + (1184519767473071/20000000000000 : ℝ)*(f.sum) + (19780847413/13750000000000000000000000 : ℝ)*base66 + (795915740968023/171875000000000000000000000000 : ℝ)*base67 + (1666241563405523/171875000000000000000000000000 : ℝ)*base69 + (1399236617551/85937500000000000000000000000 : ℝ)*base72 + (87499825843/55000000000000000000000000 : ℝ)*base73 + (640818353819949/85937500000000000000000000000 : ℝ)*base75 + (1929040455186773/171875000000000000000000000000 : ℝ)*base77 + (61358461492551/85937500000000000000000000000 : ℝ)*base80 + (87751089777/55000000000000000000000000 : ℝ)*base82 + (61798101/5000000000000000000000 : ℝ)*base90 + (61798101/5000000000000000000000 : ℝ)*base92 + (61798101/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144498412019868344283393/63593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (444971661/100000000000000 : ℝ)*(base19) + (107509953/25000000000000 : ℝ)*(base23) + (57464049/100000000000000 : ℝ)*(upper3) + (208537/100000000000000 : ℝ)*(lower4) + (45542749/100000000000000 : ℝ)*(upper5) + (44068280680299/1000000000000 : ℝ)*(major0) + (44068280680299/1000000000000 : ℝ)*(major1) + (44068280680299/1000000000000 : ℝ)*(major2) + (4447619453/50000000000000 : ℝ)*(sp1) + (4541606537/50000000000000 : ℝ)*(sp2) + (5965554629860809/100000000000000 : ℝ)*(sp4) + (2982772644825121/50000000000000 : ℝ)*(sp5) + (2982772558303961/50000000000000 : ℝ)*(sp6) + (1424050715229311/50000000000000 : ℝ)*(sp7) + (1424050715229311/50000000000000 : ℝ)*(f.failure) + (5965554629860809/100000000000000 : ℝ)*(f.sum) + (950470400039/407000000000000000000000000 : ℝ)*base65 + (1104248367477247/127187500000000000000000000000 : ℝ)*base67 + (1254967873415119/254375000000000000000000000000 : ℝ)*base69 + (832917157327247/127187500000000000000000000000 : ℝ)*base71 + (513444707801/203500000000000000000000000 : ℝ)*base73 + (142672193986689/63593750000000000000000000000 : ℝ)*base76 + (566891315294747/127187500000000000000000000000 : ℝ)*base77 + (48083596676609/15898437500000000000000000000 : ℝ)*base79 + (49467176467/40700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (10189869/5000000000000000000000 : ℝ)*base90 + (10189869/5000000000000000000000 : ℝ)*base92 + (10189869/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1342_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1342_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2463/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1342_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1342_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1342_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2463/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1342_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
