-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:19:24.477391+00:00
-- url     : https://prove2.me/submissions/e4607fe2-e659-428d-a5c1-b9d2bb1db791

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c312055_s2_s2_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1849497091/10000000000 : ℝ)*x 0 + (5733226281/10000000000 : ℝ)*x 1 + (2418077767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849497091/10000000000 : ℝ)^73 ≤ (2303267198033/20000000000000 : ℝ)^57 := by
    have hnat : (1849497091 : ℕ)^73*20000000000000^57 ≤ 2303267198033^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849497091 10000000000 2303267198033 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5733226281/10000000000 : ℝ)^73 ≤ (49043480305787/100000000000000 : ℝ)^57 := by
    have hnat : (5733226281 : ℕ)^73*100000000000000^57 ≤ 49043480305787^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5733226281 10000000000 49043480305787 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2418077767/5000000000 : ℝ)^73 ≤ (616252870169/1562500000000 : ℝ)^57 := by
    have hnat : (2418077767 : ℕ)^73*1562500000000^57 ≤ 616252870169^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418077767 5000000000 616252870169 1562500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1849497091/10000000000 : ℝ), (5733226281/10000000000 : ℝ), (2418077767/5000000000 : ℝ)] ![(2303267198033/20000000000000 : ℝ), (49043480305787/100000000000000 : ℝ), (616252870169/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1849497091/10000000000 : ℝ)|^73 ≤ (2303267198033/20000000000000 : ℝ)^57
        have hw : |(-1849497091/10000000000 : ℝ)|=(1849497091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5733226281/10000000000 : ℝ)|^73 ≤ (49043480305787/100000000000000 : ℝ)^57
        have hw : |(5733226281/10000000000 : ℝ)|=(5733226281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2418077767/5000000000 : ℝ)|^73 ≤ (616252870169/1562500000000 : ℝ)^57
        have hw : |(2418077767/5000000000 : ℝ)|=(2418077767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1550954457/2500000000 : ℝ)*x 0 + (156025351/400000000 : ℝ)*x 1 + (2366916693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1550954457/2500000000 : ℝ)^73 ≤ (27128642882643/50000000000000 : ℝ)^57 := by
    have hnat : (1550954457 : ℕ)^73*50000000000000^57 ≤ 27128642882643^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550954457 2500000000 27128642882643 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156025351/400000000 : ℝ)^73 ≤ (29947881346681/100000000000000 : ℝ)^57 := by
    have hnat : (156025351 : ℕ)^73*100000000000000^57 ≤ 29947881346681^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156025351 400000000 29947881346681 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2366916693/10000000000 : ℝ)^73 ≤ (3158966575489/20000000000000 : ℝ)^57 := by
    have hnat : (2366916693 : ℕ)^73*20000000000000^57 ≤ 3158966575489^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366916693 10000000000 3158966575489 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1550954457/2500000000 : ℝ), (156025351/400000000 : ℝ), (2366916693/10000000000 : ℝ)] ![(27128642882643/50000000000000 : ℝ), (29947881346681/100000000000000 : ℝ), (3158966575489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1550954457/2500000000 : ℝ)|^73 ≤ (27128642882643/50000000000000 : ℝ)^57
        have hw : |(1550954457/2500000000 : ℝ)|=(1550954457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156025351/400000000 : ℝ)|^73 ≤ (29947881346681/100000000000000 : ℝ)^57
        have hw : |(156025351/400000000 : ℝ)|=(156025351/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2366916693/10000000000 : ℝ)|^73 ≤ (3158966575489/20000000000000 : ℝ)^57
        have hw : |(2366916693/10000000000 : ℝ)|=(2366916693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-696125383/5000000000 : ℝ)*x 0 + (4917533033/10000000000 : ℝ)*x 1 + (1493641767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (696125383/5000000000 : ℝ)^73 ≤ (8004928475439/100000000000000 : ℝ)^57 := by
    have hnat : (696125383 : ℕ)^73*100000000000000^57 ≤ 8004928475439^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696125383 5000000000 8004928475439 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4917533033/10000000000 : ℝ)^73 ≤ (4029212831043/10000000000000 : ℝ)^57 := by
    have hnat : (4917533033 : ℕ)^73*10000000000000^57 ≤ 4029212831043^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4917533033 10000000000 4029212831043 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493641767/2500000000 : ℝ)^73 ≤ (25851471603963/50000000000000 : ℝ)^57 := by
    have hnat : (1493641767 : ℕ)^73*50000000000000^57 ≤ 25851471603963^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493641767 2500000000 25851471603963 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-696125383/5000000000 : ℝ), (4917533033/10000000000 : ℝ), (1493641767/2500000000 : ℝ)] ![(8004928475439/100000000000000 : ℝ), (4029212831043/10000000000000 : ℝ), (25851471603963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-696125383/5000000000 : ℝ)|^73 ≤ (8004928475439/100000000000000 : ℝ)^57
        have hw : |(-696125383/5000000000 : ℝ)|=(696125383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4917533033/10000000000 : ℝ)|^73 ≤ (4029212831043/10000000000000 : ℝ)^57
        have hw : |(4917533033/10000000000 : ℝ)|=(4917533033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1493641767/2500000000 : ℝ)|^73 ≤ (25851471603963/50000000000000 : ℝ)^57
        have hw : |(1493641767/2500000000 : ℝ)|=(1493641767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1129836917/2500000000 : ℝ)*x 0 + (-965599/156250000 : ℝ)*x 1 + (109858157/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1129836917/2500000000 : ℝ)^73 ≤ (18081102795557/50000000000000 : ℝ)^57 := by
    have hnat : (1129836917 : ℕ)^73*50000000000000^57 ≤ 18081102795557^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129836917 2500000000 18081102795557 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965599/156250000 : ℝ)^73 ≤ (148217706353/100000000000000 : ℝ)^57 := by
    have hnat : (965599 : ℕ)^73*100000000000000^57 ≤ 148217706353^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965599 156250000 148217706353 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109858157/156250000 : ℝ)^73 ≤ (2547583067433/4000000000000 : ℝ)^57 := by
    have hnat : (109858157 : ℕ)^73*4000000000000^57 ≤ 2547583067433^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109858157 156250000 2547583067433 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1129836917/2500000000 : ℝ), (-965599/156250000 : ℝ), (109858157/156250000 : ℝ)] ![(18081102795557/50000000000000 : ℝ), (148217706353/100000000000000 : ℝ), (2547583067433/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1129836917/2500000000 : ℝ)|^73 ≤ (18081102795557/50000000000000 : ℝ)^57
        have hw : |(1129836917/2500000000 : ℝ)|=(1129836917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-965599/156250000 : ℝ)|^73 ≤ (148217706353/100000000000000 : ℝ)^57
        have hw : |(-965599/156250000 : ℝ)|=(965599/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109858157/156250000 : ℝ)|^73 ≤ (2547583067433/4000000000000 : ℝ)^57
        have hw : |(109858157/156250000 : ℝ)|=(109858157/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4496051677/10000000000 : ℝ)*x 0 + (3361704911/5000000000 : ℝ)*x 1 + (-799203617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496051677/10000000000 : ℝ)^73 ≤ (35923647774861/100000000000000 : ℝ)^57 := by
    have hnat : (4496051677 : ℕ)^73*100000000000000^57 ≤ 35923647774861^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496051677 10000000000 35923647774861 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3361704911/5000000000 : ℝ)^73 ≤ (60144189687789/100000000000000 : ℝ)^57 := by
    have hnat : (3361704911 : ℕ)^73*100000000000000^57 ≤ 60144189687789^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3361704911 5000000000 60144189687789 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (799203617/10000000000 : ℝ)^73 ≤ (983040629663/25000000000000 : ℝ)^57 := by
    have hnat : (799203617 : ℕ)^73*25000000000000^57 ≤ 983040629663^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799203617 10000000000 983040629663 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496051677/10000000000 : ℝ), (3361704911/5000000000 : ℝ), (-799203617/10000000000 : ℝ)] ![(35923647774861/100000000000000 : ℝ), (60144189687789/100000000000000 : ℝ), (983040629663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496051677/10000000000 : ℝ)|^73 ≤ (35923647774861/100000000000000 : ℝ)^57
        have hw : |(4496051677/10000000000 : ℝ)|=(4496051677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3361704911/5000000000 : ℝ)|^73 ≤ (60144189687789/100000000000000 : ℝ)^57
        have hw : |(3361704911/5000000000 : ℝ)|=(3361704911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-799203617/10000000000 : ℝ)|^73 ≤ (983040629663/25000000000000 : ℝ)^57
        have hw : |(-799203617/10000000000 : ℝ)|=(799203617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1013342957/2000000000 : ℝ)*x 0 + (1203709509/2000000000 : ℝ)*x 1 + (551819519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013342957/2000000000 : ℝ)^73 ≤ (4186418649117/10000000000000 : ℝ)^57 := by
    have hnat : (1013342957 : ℕ)^73*10000000000000^57 ≤ 4186418649117^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013342957 2000000000 4186418649117 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203709509/2000000000 : ℝ)^73 ≤ (26095440491587/50000000000000 : ℝ)^57 := by
    have hnat : (1203709509 : ℕ)^73*50000000000000^57 ≤ 26095440491587^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203709509 2000000000 26095440491587 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551819519/5000000000 : ℝ)^73 ≤ (2972466255899/50000000000000 : ℝ)^57 := by
    have hnat : (551819519 : ℕ)^73*50000000000000^57 ≤ 2972466255899^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551819519 5000000000 2972466255899 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1013342957/2000000000 : ℝ), (1203709509/2000000000 : ℝ), (551819519/5000000000 : ℝ)] ![(4186418649117/10000000000000 : ℝ), (26095440491587/50000000000000 : ℝ), (2972466255899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1013342957/2000000000 : ℝ)|^73 ≤ (4186418649117/10000000000000 : ℝ)^57
        have hw : |(1013342957/2000000000 : ℝ)|=(1013342957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203709509/2000000000 : ℝ)|^73 ≤ (26095440491587/50000000000000 : ℝ)^57
        have hw : |(1203709509/2000000000 : ℝ)|=(1203709509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551819519/5000000000 : ℝ)|^73 ≤ (2972466255899/50000000000000 : ℝ)^57
        have hw : |(551819519/5000000000 : ℝ)|=(551819519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-636169753/10000000000 : ℝ)*x 0 + (520861941/1000000000 : ℝ)*x 1 + (6153334123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (636169753/10000000000 : ℝ)^73 ≤ (733962501107/25000000000000 : ℝ)^57 := by
    have hnat : (636169753 : ℕ)^73*25000000000000^57 ≤ 733962501107^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636169753 10000000000 733962501107 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520861941/1000000000 : ℝ)^73 ≤ (216858362063/500000000000 : ℝ)^57 := by
    have hnat : (520861941 : ℕ)^73*500000000000^57 ≤ 216858362063^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520861941 1000000000 216858362063 500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6153334123/10000000000 : ℝ)^73 ≤ (53692477575501/100000000000000 : ℝ)^57 := by
    have hnat : (6153334123 : ℕ)^73*100000000000000^57 ≤ 53692477575501^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6153334123 10000000000 53692477575501 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-636169753/10000000000 : ℝ), (520861941/1000000000 : ℝ), (6153334123/10000000000 : ℝ)] ![(733962501107/25000000000000 : ℝ), (216858362063/500000000000 : ℝ), (53692477575501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-636169753/10000000000 : ℝ)|^73 ≤ (733962501107/25000000000000 : ℝ)^57
        have hw : |(-636169753/10000000000 : ℝ)|=(636169753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520861941/1000000000 : ℝ)|^73 ≤ (216858362063/500000000000 : ℝ)^57
        have hw : |(520861941/1000000000 : ℝ)|=(520861941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6153334123/10000000000 : ℝ)|^73 ≤ (53692477575501/100000000000000 : ℝ)^57
        have hw : |(6153334123/10000000000 : ℝ)|=(6153334123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (843051981/2000000000 : ℝ)*x 0 + (-572155589/10000000000 : ℝ)*x 1 + (443046187/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843051981/2000000000 : ℝ)^73 ≤ (4134489654361/12500000000000 : ℝ)^57 := by
    have hnat : (843051981 : ℕ)^73*12500000000000^57 ≤ 4134489654361^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843051981 2000000000 4134489654361 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572155589/10000000000 : ℝ)^73 ≤ (512597142533/20000000000000 : ℝ)^57 := by
    have hnat : (572155589 : ℕ)^73*20000000000000^57 ≤ 512597142533^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572155589 10000000000 512597142533 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443046187/625000000 : ℝ)^73 ≤ (6436109703841/10000000000000 : ℝ)^57 := by
    have hnat : (443046187 : ℕ)^73*10000000000000^57 ≤ 6436109703841^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443046187 625000000 6436109703841 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843051981/2000000000 : ℝ), (-572155589/10000000000 : ℝ), (443046187/625000000 : ℝ)] ![(4134489654361/12500000000000 : ℝ), (512597142533/20000000000000 : ℝ), (6436109703841/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843051981/2000000000 : ℝ)|^73 ≤ (4134489654361/12500000000000 : ℝ)^57
        have hw : |(843051981/2000000000 : ℝ)|=(843051981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-572155589/10000000000 : ℝ)|^73 ≤ (512597142533/20000000000000 : ℝ)^57
        have hw : |(-572155589/10000000000 : ℝ)|=(572155589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(443046187/625000000 : ℝ)|^73 ≤ (6436109703841/10000000000000 : ℝ)^57
        have hw : |(443046187/625000000 : ℝ)|=(443046187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1220642441/2000000000 : ℝ)*x 0 + (5269670529/10000000000 : ℝ)*x 1 + (-620437239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1220642441/2000000000 : ℝ)^73 ≤ (53133002327309/100000000000000 : ℝ)^57 := by
    have hnat : (1220642441 : ℕ)^73*100000000000000^57 ≤ 53133002327309^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220642441 2000000000 53133002327309 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5269670529/10000000000 : ℝ)^73 ≤ (44023806712289/100000000000000 : ℝ)^57 := by
    have hnat : (5269670529 : ℕ)^73*100000000000000^57 ≤ 44023806712289^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269670529 10000000000 44023806712289 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (620437239/10000000000 : ℝ)^73 ≤ (2843190941469/100000000000000 : ℝ)^57 := by
    have hnat : (620437239 : ℕ)^73*100000000000000^57 ≤ 2843190941469^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620437239 10000000000 2843190941469 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1220642441/2000000000 : ℝ), (5269670529/10000000000 : ℝ), (-620437239/10000000000 : ℝ)] ![(53133002327309/100000000000000 : ℝ), (44023806712289/100000000000000 : ℝ), (2843190941469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1220642441/2000000000 : ℝ)|^73 ≤ (53133002327309/100000000000000 : ℝ)^57
        have hw : |(1220642441/2000000000 : ℝ)|=(1220642441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5269670529/10000000000 : ℝ)|^73 ≤ (44023806712289/100000000000000 : ℝ)^57
        have hw : |(5269670529/10000000000 : ℝ)|=(5269670529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-620437239/10000000000 : ℝ)|^73 ≤ (2843190941469/100000000000000 : ℝ)^57
        have hw : |(-620437239/10000000000 : ℝ)|=(620437239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7767800333/10000000000 : ℝ)*x 0 + (626407147/2000000000 : ℝ)*x 1 + (19368919/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7767800333/10000000000 : ℝ)^73 ≤ (2261281067587/3125000000000 : ℝ)^57 := by
    have hnat : (7767800333 : ℕ)^73*3125000000000^57 ≤ 2261281067587^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7767800333 10000000000 2261281067587 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626407147/2000000000 : ℝ)^73 ≤ (22610198808923/100000000000000 : ℝ)^57 := by
    have hnat : (626407147 : ℕ)^73*100000000000000^57 ≤ 22610198808923^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626407147 2000000000 22610198808923 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19368919/200000000 : ℝ)^73 ≤ (5028807017241/100000000000000 : ℝ)^57 := by
    have hnat : (19368919 : ℕ)^73*100000000000000^57 ≤ 5028807017241^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19368919 200000000 5028807017241 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7767800333/10000000000 : ℝ), (626407147/2000000000 : ℝ), (19368919/200000000 : ℝ)] ![(2261281067587/3125000000000 : ℝ), (22610198808923/100000000000000 : ℝ), (5028807017241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7767800333/10000000000 : ℝ)|^73 ≤ (2261281067587/3125000000000 : ℝ)^57
        have hw : |(7767800333/10000000000 : ℝ)|=(7767800333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626407147/2000000000 : ℝ)|^73 ≤ (22610198808923/100000000000000 : ℝ)^57
        have hw : |(626407147/2000000000 : ℝ)|=(626407147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19368919/200000000 : ℝ)|^73 ≤ (5028807017241/100000000000000 : ℝ)^57
        have hw : |(19368919/200000000 : ℝ)|=(19368919/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-133629161/2000000000 : ℝ)*x 0 + (323837471/500000000 : ℝ)*x 1 + (4845790151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133629161/2000000000 : ℝ)^73 ≤ (781538814539/25000000000000 : ℝ)^57 := by
    have hnat : (133629161 : ℕ)^73*25000000000000^57 ≤ 781538814539^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133629161 2000000000 781538814539 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323837471/500000000 : ℝ)^73 ≤ (57333004390837/100000000000000 : ℝ)^57 := by
    have hnat : (323837471 : ℕ)^73*100000000000000^57 ≤ 57333004390837^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323837471 500000000 57333004390837 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4845790151/10000000000 : ℝ)^73 ≤ (4942605043/12500000000 : ℝ)^57 := by
    have hnat : (4845790151 : ℕ)^73*12500000000^57 ≤ 4942605043^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4845790151 10000000000 4942605043 12500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133629161/2000000000 : ℝ), (323837471/500000000 : ℝ), (4845790151/10000000000 : ℝ)] ![(781538814539/25000000000000 : ℝ), (57333004390837/100000000000000 : ℝ), (4942605043/12500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133629161/2000000000 : ℝ)|^73 ≤ (781538814539/25000000000000 : ℝ)^57
        have hw : |(-133629161/2000000000 : ℝ)|=(133629161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323837471/500000000 : ℝ)|^73 ≤ (57333004390837/100000000000000 : ℝ)^57
        have hw : |(323837471/500000000 : ℝ)|=(323837471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4845790151/10000000000 : ℝ)|^73 ≤ (4942605043/12500000000 : ℝ)^57
        have hw : |(4845790151/10000000000 : ℝ)|=(4845790151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1523633033/2500000000 : ℝ)*x 0 + (-2634499/400000000 : ℝ)*x 1 + (5527669253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1523633033/2500000000 : ℝ)^73 ≤ (13259060878063/25000000000000 : ℝ)^57 := by
    have hnat : (1523633033 : ℕ)^73*25000000000000^57 ≤ 13259060878063^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523633033 2500000000 13259060878063 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2634499/400000000 : ℝ)^73 ≤ (10050922791/6250000000000 : ℝ)^57 := by
    have hnat : (2634499 : ℕ)^73*6250000000000^57 ≤ 10050922791^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634499 400000000 10050922791 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527669253/10000000000 : ℝ)^73 ≤ (9360588343449/20000000000000 : ℝ)^57 := by
    have hnat : (5527669253 : ℕ)^73*20000000000000^57 ≤ 9360588343449^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527669253 10000000000 9360588343449 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1523633033/2500000000 : ℝ), (-2634499/400000000 : ℝ), (5527669253/10000000000 : ℝ)] ![(13259060878063/25000000000000 : ℝ), (10050922791/6250000000000 : ℝ), (9360588343449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1523633033/2500000000 : ℝ)|^73 ≤ (13259060878063/25000000000000 : ℝ)^57
        have hw : |(1523633033/2500000000 : ℝ)|=(1523633033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2634499/400000000 : ℝ)|^73 ≤ (10050922791/6250000000000 : ℝ)^57
        have hw : |(-2634499/400000000 : ℝ)|=(2634499/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527669253/10000000000 : ℝ)|^73 ≤ (9360588343449/20000000000000 : ℝ)^57
        have hw : |(5527669253/10000000000 : ℝ)|=(5527669253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2120370537/5000000000 : ℝ)*x 0 + (335967287/500000000 : ℝ)*x 1 + (-119326697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120370537/5000000000 : ℝ)^73 ≤ (33332201927097/100000000000000 : ℝ)^57 := by
    have hnat : (2120370537 : ℕ)^73*100000000000000^57 ≤ 33332201927097^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120370537 5000000000 33332201927097 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335967287/500000000 : ℝ)^73 ≤ (12019526693619/20000000000000 : ℝ)^57 := by
    have hnat : (335967287 : ℕ)^73*20000000000000^57 ≤ 12019526693619^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335967287 500000000 12019526693619 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119326697/1000000000 : ℝ)^73 ≤ (1314032918383/20000000000000 : ℝ)^57 := by
    have hnat : (119326697 : ℕ)^73*20000000000000^57 ≤ 1314032918383^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119326697 1000000000 1314032918383 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120370537/5000000000 : ℝ), (335967287/500000000 : ℝ), (-119326697/1000000000 : ℝ)] ![(33332201927097/100000000000000 : ℝ), (12019526693619/20000000000000 : ℝ), (1314032918383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120370537/5000000000 : ℝ)|^73 ≤ (33332201927097/100000000000000 : ℝ)^57
        have hw : |(2120370537/5000000000 : ℝ)|=(2120370537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(335967287/500000000 : ℝ)|^73 ≤ (12019526693619/20000000000000 : ℝ)^57
        have hw : |(335967287/500000000 : ℝ)|=(335967287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-119326697/1000000000 : ℝ)|^73 ≤ (1314032918383/20000000000000 : ℝ)^57
        have hw : |(-119326697/1000000000 : ℝ)|=(119326697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s2_s2_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (19134361/25000000 : ℝ)*x 0 + (148293477/625000000 : ℝ)*x 1 + (2051668229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19134361/25000000 : ℝ)^73 ≤ (7100307704199/10000000000000 : ℝ)^57 := by
    have hnat : (19134361 : ℕ)^73*10000000000000^57 ≤ 7100307704199^57*25000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19134361 25000000 7100307704199 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148293477/625000000 : ℝ)^73 ≤ (792211927899/5000000000000 : ℝ)^57 := by
    have hnat : (148293477 : ℕ)^73*5000000000000^57 ≤ 792211927899^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148293477 625000000 792211927899 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051668229/10000000000 : ℝ)^73 ≤ (1644085547871/12500000000000 : ℝ)^57 := by
    have hnat : (2051668229 : ℕ)^73*12500000000000^57 ≤ 1644085547871^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051668229 10000000000 1644085547871 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19134361/25000000 : ℝ), (148293477/625000000 : ℝ), (2051668229/10000000000 : ℝ)] ![(7100307704199/10000000000000 : ℝ), (792211927899/5000000000000 : ℝ), (1644085547871/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19134361/25000000 : ℝ)|^73 ≤ (7100307704199/10000000000000 : ℝ)^57
        have hw : |(19134361/25000000 : ℝ)|=(19134361/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148293477/625000000 : ℝ)|^73 ≤ (792211927899/5000000000000 : ℝ)^57
        have hw : |(148293477/625000000 : ℝ)|=(148293477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2051668229/10000000000 : ℝ)|^73 ≤ (1644085547871/12500000000000 : ℝ)^57
        have hw : |(2051668229/10000000000 : ℝ)|=(2051668229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312055_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((69521/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69521/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33723/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33723/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13743/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13743/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((24389/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24389/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(617/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(617/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6257/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (69521/100000 : ℝ) ^ (9/2 : ℝ) ≤ (19476999225004604187/100000000000000000000 : ℝ) := by
    have hpowers : (69521/100000 : ℝ)^9 ≤ (19476999225004604187/100000000000000000000 : ℝ)^2 := by
      have hnat : (69521 : ℕ)^9*100000000000000000000^2 ≤ 19476999225004604187^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69521 100000 19476999225004604187 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69521/100000 : ℝ)) (X := (19476999225004604187/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0a : (119476999225004604187/100000000000000000000 : ℝ) ≤ (2600843971318731/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (119476999225004604187/100000000000000000000 : ℝ)^2 ≤ (2600843971318731/2500000000000000 : ℝ)^9 := by
      have hnat : (119476999225004604187 : ℕ)^2*2500000000000000^9 ≤ 2600843971318731^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119476999225004604187 100000000000000000000 2600843971318731 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2600843971318731/2500000000000000 : ℝ)) (X := (119476999225004604187/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0b : (69476999225004604187/50000000000000000000 : ℝ) ≤ (10758435533556497/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (69476999225004604187/50000000000000000000 : ℝ)^2 ≤ (10758435533556497/10000000000000000 : ℝ)^9 := by
      have hnat : (69476999225004604187 : ℕ)^2*10000000000000000^9 ≤ 10758435533556497^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69476999225004604187 50000000000000000000 10758435533556497 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10758435533556497/10000000000000000 : ℝ)) (X := (69476999225004604187/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(100843971318731/1738025000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(355059648281573/6952100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (69521/100000 : ℝ)) (alpha := (100843971318731/1738025000000000 : ℝ)) (beta := (355059648281573/6952100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (69521/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(100843971318731/1738025000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(355059648281573/6952100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (33723/50000 : ℝ) ^ (9/2 : ℝ) ≤ (849714239515161013/5000000000000000000 : ℝ) := by
    have hpowers : (33723/50000 : ℝ)^9 ≤ (849714239515161013/5000000000000000000 : ℝ)^2 := by
      have hnat : (33723 : ℕ)^9*5000000000000000000^2 ≤ 849714239515161013^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33723 50000 849714239515161013 5000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33723/50000 : ℝ)) (X := (849714239515161013/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1a : (5849714239515161013/5000000000000000000 : ℝ) ≤ (10354942682540599/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (5849714239515161013/5000000000000000000 : ℝ)^2 ≤ (10354942682540599/10000000000000000 : ℝ)^9 := by
      have hnat : (5849714239515161013 : ℕ)^2*10000000000000000^9 ≤ 10354942682540599^9*5000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5849714239515161013 5000000000000000000 10354942682540599 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10354942682540599/10000000000000000 : ℝ)) (X := (5849714239515161013/5000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1b : (3349714239515161013/2500000000000000000 : ℝ) ≤ (1067179018077339/1000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3349714239515161013/2500000000000000000 : ℝ)^2 ≤ (1067179018077339/1000000000000000 : ℝ)^9 := by
      have hnat : (3349714239515161013 : ℕ)^2*1000000000000000^9 ≤ 1067179018077339^9*2500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3349714239515161013 2500000000000000000 1067179018077339 1000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1067179018077339/1000000000000000 : ℝ)) (X := (3349714239515161013/2500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(118314227513533/2248200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(316847498232791/6744600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (33723/50000 : ℝ)) (alpha := (118314227513533/2248200000000000 : ℝ)) (beta := (316847498232791/6744600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (33723/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(118314227513533/2248200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(316847498232791/6744600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (13743/20000 : ℝ) ^ (9/2 : ℝ) ≤ (18481277101917278829/100000000000000000000 : ℝ) := by
    have hpowers : (13743/20000 : ℝ)^9 ≤ (18481277101917278829/100000000000000000000 : ℝ)^2 := by
      have hnat : (13743 : ℕ)^9*100000000000000000000^2 ≤ 18481277101917278829^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13743 20000 18481277101917278829 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13743/20000 : ℝ)) (X := (18481277101917278829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2a : (118481277101917278829/100000000000000000000 : ℝ) ≤ (2076809212524957/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (118481277101917278829/100000000000000000000 : ℝ)^2 ≤ (2076809212524957/2000000000000000 : ℝ)^9 := by
      have hnat : (118481277101917278829 : ℕ)^2*2000000000000000^9 ≤ 2076809212524957^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118481277101917278829 100000000000000000000 2076809212524957 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2076809212524957/2000000000000000 : ℝ)) (X := (118481277101917278829/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2b : (68481277101917278829/50000000000000000000 : ℝ) ≤ (1072397927241449/1000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (68481277101917278829/50000000000000000000 : ℝ)^2 ≤ (1072397927241449/1000000000000000 : ℝ)^9 := by
      have hnat : (68481277101917278829 : ℕ)^2*1000000000000000^9 ≤ 1072397927241449^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68481277101917278829 50000000000000000000 1072397927241449 1000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1072397927241449/1000000000000000 : ℝ)) (X := (68481277101917278829/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(76809212524957/1374300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(67986641957941/1374300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (13743/20000 : ℝ)) (alpha := (76809212524957/1374300000000000 : ℝ)) (beta := (67986641957941/1374300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13743/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(76809212524957/1374300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(67986641957941/1374300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1849497091/10000000000 : ℝ)*X 0 0+(5733226281/10000000000 : ℝ)*X 0 1+(2418077767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1550954457/2500000000 : ℝ)*X 0 0+(156025351/400000000 : ℝ)*X 0 1+(2366916693/10000000000 : ℝ)*X 0 2+(1550954457/2500000000 : ℝ)*X 1 0+(156025351/400000000 : ℝ)*X 1 1+(2366916693/10000000000 : ℝ)*X 1 2+(1550954457/2500000000 : ℝ)*X 2 0+(156025351/400000000 : ℝ)*X 2 1+(2366916693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-696125383/5000000000 : ℝ)*X 0 0+(4917533033/10000000000 : ℝ)*X 0 1+(1493641767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1129836917/2500000000 : ℝ)*X 1 0+(-965599/156250000 : ℝ)*X 1 1+(109858157/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4496051677/10000000000 : ℝ)*X 2 0+(3361704911/5000000000 : ℝ)*X 2 1+(-799203617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1013342957/2000000000 : ℝ)*X 0 0+(1203709509/2000000000 : ℝ)*X 0 1+(551819519/5000000000 : ℝ)*X 0 2+(1013342957/2000000000 : ℝ)*X 1 0+(1203709509/2000000000 : ℝ)*X 1 1+(551819519/5000000000 : ℝ)*X 1 2+(1013342957/2000000000 : ℝ)*X 2 0+(1203709509/2000000000 : ℝ)*X 2 1+(551819519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-636169753/10000000000 : ℝ)*X 0 0+(520861941/1000000000 : ℝ)*X 0 1+(6153334123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((843051981/2000000000 : ℝ)*X 1 0+(-572155589/10000000000 : ℝ)*X 1 1+(443046187/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1220642441/2000000000 : ℝ)*X 2 0+(5269670529/10000000000 : ℝ)*X 2 1+(-620437239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7767800333/10000000000 : ℝ)*X 0 0+(626407147/2000000000 : ℝ)*X 0 1+(19368919/200000000 : ℝ)*X 0 2+(7767800333/10000000000 : ℝ)*X 1 0+(626407147/2000000000 : ℝ)*X 1 1+(19368919/200000000 : ℝ)*X 1 2+(7767800333/10000000000 : ℝ)*X 2 0+(626407147/2000000000 : ℝ)*X 2 1+(19368919/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-133629161/2000000000 : ℝ)*X 0 0+(323837471/500000000 : ℝ)*X 0 1+(4845790151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1523633033/2500000000 : ℝ)*X 1 0+(-2634499/400000000 : ℝ)*X 1 1+(5527669253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2120370537/5000000000 : ℝ)*X 2 0+(335967287/500000000 : ℝ)*X 2 1+(-119326697/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((19134361/25000000 : ℝ)*X 0 0+(148293477/625000000 : ℝ)*X 0 1+(2051668229/10000000000 : ℝ)*X 0 2+(19134361/25000000 : ℝ)*X 1 0+(148293477/625000000 : ℝ)*X 1 1+(2051668229/10000000000 : ℝ)*X 1 2+(19134361/25000000 : ℝ)*X 2 0+(148293477/625000000 : ℝ)*X 2 1+(2051668229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((24389/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24389/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7034640001722786812653/635741000000000000000000000 : ℝ) := by norm_num
    linear_combination (5479249/1000000000000 : ℝ)*(base19) + (10214452773/50000000000 : ℝ)*(base49) + (2045578928061/500000000000 : ℝ)*(major_s2_0) + (2045578928061/500000000000 : ℝ)*(major_s2_1) + (2045578928061/500000000000 : ℝ)*(major_s2_2) + (13853997/500000000000 : ℝ)*(sp_s2_0) + (2666381/500000000000 : ℝ)*(sp_s2_6) + (5731207071113/1000000000000 : ℝ)*(sp_s2_7) + (9169891319/1600000000 : ℝ)*(sp_s2_8) + (1432770262247/250000000000 : ℝ)*(sp_s2_9) + (612766674113/250000000000 : ℝ)*(sp_s2_13) + (52440979/1000000000000 : ℝ)*(sp_s2_15) + (2607749/500000000000 : ℝ)*(sp_s2_21) + (9934101/62500000000 : ℝ)*(sp_s2_23) + (1225536014607/500000000000 : ℝ)*(f.failure) + (1432809998651/250000000000 : ℝ)*(f.sum) + (119626886983207439/572166900000000000000000000000 : ℝ)*base63 + (83343456561349/114525000000000000000000000 : ℝ)*base64 + (1238974844706617/1124100000000000000000000000 : ℝ)*base66 + (2527899262519/14315625000000000000000000 : ℝ)*base69 + (44611045045961249/3980946262500000000000000000000 : ℝ)*base71 + (2255913084391903/3476050000000000000000000000 : ℝ)*base73 + (42561415870349/374700000000000000000000000 : ℝ)*base74 + (243272179696783/1738025000000000000000000000 : ℝ)*base76 + (31611019233057202771/78148556100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (1809/50000000000000000 : ℝ)*base86 + (1809/50000000000000000 : ℝ)*base88 + (1809/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(617/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(617/1250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9829865633606977088631427/1326982087500000000000000000000 : ℝ) := by norm_num
    linear_combination (602871/200000000000 : ℝ)*(base21) + (828859/500000000000 : ℝ)*(base39) + (123210054117/1000000000000 : ℝ)*(base49) + (4949/31250000000 : ℝ)*(base60) + (1867456006391/500000000000 : ℝ)*(major_s2_0) + (1867456006391/500000000000 : ℝ)*(major_s2_1) + (1867456006391/500000000000 : ℝ)*(major_s2_2) + (3698739/500000000000 : ℝ)*(sp_s2_7) + (37145547/1000000000000 : ℝ)*(sp_s2_8) + (523217418307/100000000000 : ℝ)*(sp_s2_14) + (5232144435001/1000000000000 : ℝ)*(sp_s2_15) + (5232178566193/1000000000000 : ℝ)*(sp_s2_16) + (223760222779/100000000000 : ℝ)*(sp_s2_20) + (7549599/200000000000 : ℝ)*(sp_s2_27) + (447527995157/200000000000 : ℝ)*(f.failure) + (1308045395137/250000000000 : ℝ)*(f.sum) + (664837784267730667/1716500700000000000000000000000 : ℝ)*base63 + (327699030620329/687150000000000000000000000 : ℝ)*base64 + (41212427118151/3372300000000000000000000000 : ℝ)*base66 + (48917232645961/343575000000000000000000000 : ℝ)*base69 + (1499519673805845259/5971419393750000000000000000000 : ℝ)*base70 + (157169851381807/869012500000000000000000000 : ℝ)*base73 + (106844858360947/1124100000000000000000000000 : ℝ)*base74 + (1042266292199851/3476050000000000000000000000 : ℝ)*base76 + (169117103040848038537/234445668300000000000000000000000 : ℝ)*base79 + (341/20000000000000000 : ℝ)*base87 + (341/20000000000000000 : ℝ)*base89 + (341/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6257/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (46876661282590882667831/5820096875000000000000000000 : ℝ) := by norm_num
    linear_combination (33459/1000000000000 : ℝ)*(base23) + (49591493171/500000000000 : ℝ)*(base40) + (5583072441/62500000000 : ℝ)*(base49) + (921841/500000000000 : ℝ)*(base59) + (3899682123963/1000000000000 : ℝ)*(major_s2_0) + (3899682123963/1000000000000 : ℝ)*(major_s2_1) + (3899682123963/1000000000000 : ℝ)*(major_s2_2) + (17268129/1000000000000 : ℝ)*(sp_s2_0) + (3730439/200000000000 : ℝ)*(sp_s2_9) + (245703/4000000000 : ℝ)*(sp_s2_20) + (682873519379/125000000000 : ℝ)*(sp_s2_21) + (136575135579/25000000000 : ℝ)*(sp_s2_22) + (5462986737507/1000000000000 : ℝ)*(sp_s2_23) + (2336294714253/1000000000000 : ℝ)*(sp_s2_27) + (2336356140003/1000000000000 : ℝ)*(f.failure) + (136575135579/25000000000 : ℝ)*(f.sum) + (35644468929482737/1144333800000000000000000000000 : ℝ)*base63 + (274646878551289/458100000000000000000000000 : ℝ)*base64 + (244131859724011/2248200000000000000000000000 : ℝ)*base66 + (27013118691497/458100000000000000000000000 : ℝ)*base69 + (243379241034143153/1676187900000000000000000000000 : ℝ)*base70 + (28194971975591/365900000000000000000000000 : ℝ)*base73 + (257237005438927/749400000000000000000000000 : ℝ)*base74 + (60676119920073/91475000000000000000000000 : ℝ)*base76 + (3308270636460841813/8226163800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (20739/100000000000000000 : ℝ)*base87 + (20739/100000000000000000 : ℝ)*base89 + (20739/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((69521/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69521/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33723/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33723/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13743/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13743/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((24389/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24389/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(617/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(617/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6257/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312055_s2 p hpa hpb X hX hprev1

#print axioms solution
