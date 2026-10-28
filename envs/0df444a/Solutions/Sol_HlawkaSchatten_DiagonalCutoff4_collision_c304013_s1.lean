-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304013_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:36:43.140513+00:00
-- url     : https://prove2.me/submissions/ed11d6d1-e6ac-479f-b829-5c6f248ad557

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
theorem collision_support_c304013_s1_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3189020823/5000000000 : ℝ)*x 0 + (1480516189/5000000000 : ℝ)*x 1 + (1684223599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3189020823/5000000000 : ℝ)^17 ≤ (55538116977779/100000000000000 : ℝ)^13 := by
    have hnat : (3189020823 : ℕ)^17*100000000000000^13 ≤ 55538116977779^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189020823 5000000000 55538116977779 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1480516189/5000000000 : ℝ)^17 ≤ (20361524035957/100000000000000 : ℝ)^13 := by
    have hnat : (1480516189 : ℕ)^17*100000000000000^13 ≤ 20361524035957^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480516189 5000000000 20361524035957 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684223599/5000000000 : ℝ)^17 ≤ (24100358969707/100000000000000 : ℝ)^13 := by
    have hnat : (1684223599 : ℕ)^17*100000000000000^13 ≤ 24100358969707^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684223599 5000000000 24100358969707 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3189020823/5000000000 : ℝ), (1480516189/5000000000 : ℝ), (1684223599/5000000000 : ℝ)] ![(55538116977779/100000000000000 : ℝ), (20361524035957/100000000000000 : ℝ), (24100358969707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3189020823/5000000000 : ℝ)|^17 ≤ (55538116977779/100000000000000 : ℝ)^13
        have hw : |(3189020823/5000000000 : ℝ)|=(3189020823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1480516189/5000000000 : ℝ)|^17 ≤ (20361524035957/100000000000000 : ℝ)^13
        have hw : |(1480516189/5000000000 : ℝ)|=(1480516189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1684223599/5000000000 : ℝ)|^17 ≤ (24100358969707/100000000000000 : ℝ)^13
        have hw : |(1684223599/5000000000 : ℝ)|=(1684223599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1010434999/2500000000 : ℝ)*x 0 + (-507755791/1250000000 : ℝ)*x 1 + (-2415875663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010434999/2500000000 : ℝ)^17 ≤ (15292640908739/50000000000000 : ℝ)^13 := by
    have hnat : (1010434999 : ℕ)^17*50000000000000^13 ≤ 15292640908739^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010434999 2500000000 15292640908739 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507755791/1250000000 : ℝ)^17 ≤ (6157276758413/20000000000000 : ℝ)^13 := by
    have hnat : (507755791 : ℕ)^17*20000000000000^13 ≤ 6157276758413^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507755791 1250000000 6157276758413 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2415875663/5000000000 : ℝ)^17 ≤ (1931416718567/5000000000000 : ℝ)^13 := by
    have hnat : (2415875663 : ℕ)^17*5000000000000^13 ≤ 1931416718567^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415875663 5000000000 1931416718567 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1010434999/2500000000 : ℝ), (-507755791/1250000000 : ℝ), (-2415875663/5000000000 : ℝ)] ![(15292640908739/50000000000000 : ℝ), (6157276758413/20000000000000 : ℝ), (1931416718567/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1010434999/2500000000 : ℝ)|^17 ≤ (15292640908739/50000000000000 : ℝ)^13
        have hw : |(1010434999/2500000000 : ℝ)|=(1010434999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507755791/1250000000 : ℝ)|^17 ≤ (6157276758413/20000000000000 : ℝ)^13
        have hw : |(-507755791/1250000000 : ℝ)|=(507755791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2415875663/5000000000 : ℝ)|^17 ≤ (1931416718567/5000000000000 : ℝ)^13
        have hw : |(-2415875663/5000000000 : ℝ)|=(2415875663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3034623353/10000000000 : ℝ)*x 0 + (-2875028479/10000000000 : ℝ)*x 1 + (1678246503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3034623353/10000000000 : ℝ)^17 ≤ (4205158993069/20000000000000 : ℝ)^13 := by
    have hnat : (3034623353 : ℕ)^17*20000000000000^13 ≤ 4205158993069^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3034623353 10000000000 4205158993069 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2875028479/10000000000 : ℝ)^17 ≤ (19591627062999/100000000000000 : ℝ)^13 := by
    have hnat : (2875028479 : ℕ)^17*100000000000000^13 ≤ 19591627062999^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2875028479 10000000000 19591627062999 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678246503/2500000000 : ℝ)^17 ≤ (11876515590923/20000000000000 : ℝ)^13 := by
    have hnat : (1678246503 : ℕ)^17*20000000000000^13 ≤ 11876515590923^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678246503 2500000000 11876515590923 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3034623353/10000000000 : ℝ), (-2875028479/10000000000 : ℝ), (1678246503/2500000000 : ℝ)] ![(4205158993069/20000000000000 : ℝ), (19591627062999/100000000000000 : ℝ), (11876515590923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3034623353/10000000000 : ℝ)|^17 ≤ (4205158993069/20000000000000 : ℝ)^13
        have hw : |(3034623353/10000000000 : ℝ)|=(3034623353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2875028479/10000000000 : ℝ)|^17 ≤ (19591627062999/100000000000000 : ℝ)^13
        have hw : |(-2875028479/10000000000 : ℝ)|=(2875028479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1678246503/2500000000 : ℝ)|^17 ≤ (11876515590923/20000000000000 : ℝ)^13
        have hw : |(1678246503/2500000000 : ℝ)|=(1678246503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2490295939/10000000000 : ℝ)*x 0 + (-7229745329/10000000000 : ℝ)*x 1 + (1366401519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2490295939/10000000000 : ℝ)^17 ≤ (4059027874611/25000000000000 : ℝ)^13 := by
    have hnat : (2490295939 : ℕ)^17*25000000000000^13 ≤ 4059027874611^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490295939 10000000000 4059027874611 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7229745329/10000000000 : ℝ)^17 ≤ (65429895988327/100000000000000 : ℝ)^13 := by
    have hnat : (7229745329 : ℕ)^17*100000000000000^13 ≤ 65429895988327^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7229745329 10000000000 65429895988327 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366401519/5000000000 : ℝ)^17 ≤ (9166996248507/50000000000000 : ℝ)^13 := by
    have hnat : (1366401519 : ℕ)^17*50000000000000^13 ≤ 9166996248507^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366401519 5000000000 9166996248507 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2490295939/10000000000 : ℝ), (-7229745329/10000000000 : ℝ), (1366401519/5000000000 : ℝ)] ![(4059027874611/25000000000000 : ℝ), (65429895988327/100000000000000 : ℝ), (9166996248507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2490295939/10000000000 : ℝ)|^17 ≤ (4059027874611/25000000000000 : ℝ)^13
        have hw : |(-2490295939/10000000000 : ℝ)|=(2490295939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7229745329/10000000000 : ℝ)|^17 ≤ (65429895988327/100000000000000 : ℝ)^13
        have hw : |(-7229745329/10000000000 : ℝ)|=(7229745329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366401519/5000000000 : ℝ)|^17 ≤ (9166996248507/50000000000000 : ℝ)^13
        have hw : |(1366401519/5000000000 : ℝ)|=(1366401519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6349286639/10000000000 : ℝ)*x 0 + (3030119391/10000000000 : ℝ)*x 1 + (1668367973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6349286639/10000000000 : ℝ)^17 ≤ (55210911022809/100000000000000 : ℝ)^13 := by
    have hnat : (6349286639 : ℕ)^17*100000000000000^13 ≤ 55210911022809^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6349286639 10000000000 55210911022809 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3030119391/10000000000 : ℝ)^17 ≤ (2623124505217/12500000000000 : ℝ)^13 := by
    have hnat : (3030119391 : ℕ)^17*12500000000000^13 ≤ 2623124505217^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030119391 10000000000 2623124505217 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1668367973/5000000000 : ℝ)^17 ≤ (2380409291807/10000000000000 : ℝ)^13 := by
    have hnat : (1668367973 : ℕ)^17*10000000000000^13 ≤ 2380409291807^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668367973 5000000000 2380409291807 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6349286639/10000000000 : ℝ), (3030119391/10000000000 : ℝ), (1668367973/5000000000 : ℝ)] ![(55210911022809/100000000000000 : ℝ), (2623124505217/12500000000000 : ℝ), (2380409291807/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6349286639/10000000000 : ℝ)|^17 ≤ (55210911022809/100000000000000 : ℝ)^13
        have hw : |(6349286639/10000000000 : ℝ)|=(6349286639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3030119391/10000000000 : ℝ)|^17 ≤ (2623124505217/12500000000000 : ℝ)^13
        have hw : |(3030119391/10000000000 : ℝ)|=(3030119391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1668367973/5000000000 : ℝ)|^17 ≤ (2380409291807/10000000000000 : ℝ)^13
        have hw : |(1668367973/5000000000 : ℝ)|=(1668367973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1032378913/2500000000 : ℝ)*x 0 + (-2009878793/5000000000 : ℝ)*x 1 + (-2394178441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032378913/2500000000 : ℝ)^17 ≤ (31456777415051/100000000000000 : ℝ)^13 := by
    have hnat : (1032378913 : ℕ)^17*100000000000000^13 ≤ 31456777415051^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032378913 2500000000 31456777415051 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009878793/5000000000 : ℝ)^17 ≤ (30367931147351/100000000000000 : ℝ)^13 := by
    have hnat : (2009878793 : ℕ)^17*100000000000000^13 ≤ 30367931147351^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009878793 5000000000 30367931147351 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394178441/5000000000 : ℝ)^17 ≤ (19087645713191/50000000000000 : ℝ)^13 := by
    have hnat : (2394178441 : ℕ)^17*50000000000000^13 ≤ 19087645713191^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394178441 5000000000 19087645713191 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1032378913/2500000000 : ℝ), (-2009878793/5000000000 : ℝ), (-2394178441/5000000000 : ℝ)] ![(31456777415051/100000000000000 : ℝ), (30367931147351/100000000000000 : ℝ), (19087645713191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1032378913/2500000000 : ℝ)|^17 ≤ (31456777415051/100000000000000 : ℝ)^13
        have hw : |(1032378913/2500000000 : ℝ)|=(1032378913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2009878793/5000000000 : ℝ)|^17 ≤ (30367931147351/100000000000000 : ℝ)^13
        have hw : |(-2009878793/5000000000 : ℝ)|=(2009878793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2394178441/5000000000 : ℝ)|^17 ≤ (19087645713191/50000000000000 : ℝ)^13
        have hw : |(-2394178441/5000000000 : ℝ)|=(2394178441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1166521571/5000000000 : ℝ)*x 0 + (-1285451439/10000000000 : ℝ)*x 1 + (8290140139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1166521571/5000000000 : ℝ)^17 ≤ (14908620781909/100000000000000 : ℝ)^13 := by
    have hnat : (1166521571 : ℕ)^17*100000000000000^13 ≤ 14908620781909^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166521571 5000000000 14908620781909 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285451439/10000000000 : ℝ)^17 ≤ (3418920195931/50000000000000 : ℝ)^13 := by
    have hnat : (1285451439 : ℕ)^17*50000000000000^13 ≤ 3418920195931^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285451439 10000000000 3418920195931 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8290140139/10000000000 : ℝ)^17 ≤ (2445423088087/3125000000000 : ℝ)^13 := by
    have hnat : (8290140139 : ℕ)^17*3125000000000^13 ≤ 2445423088087^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8290140139 10000000000 2445423088087 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1166521571/5000000000 : ℝ), (-1285451439/10000000000 : ℝ), (8290140139/10000000000 : ℝ)] ![(14908620781909/100000000000000 : ℝ), (3418920195931/50000000000000 : ℝ), (2445423088087/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1166521571/5000000000 : ℝ)|^17 ≤ (14908620781909/100000000000000 : ℝ)^13
        have hw : |(1166521571/5000000000 : ℝ)|=(1166521571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1285451439/10000000000 : ℝ)|^17 ≤ (3418920195931/50000000000000 : ℝ)^13
        have hw : |(-1285451439/10000000000 : ℝ)|=(1285451439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8290140139/10000000000 : ℝ)|^17 ≤ (2445423088087/3125000000000 : ℝ)^13
        have hw : |(8290140139/10000000000 : ℝ)|=(8290140139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1488730127/5000000000 : ℝ)*x 0 + (-6379612457/10000000000 : ℝ)*x 1 + (1675359263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1488730127/5000000000 : ℝ)^17 ≤ (20509375002357/100000000000000 : ℝ)^13 := by
    have hnat : (1488730127 : ℕ)^17*100000000000000^13 ≤ 20509375002357^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488730127 5000000000 20509375002357 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6379612457/10000000000 : ℝ)^17 ≤ (5555600448233/10000000000000 : ℝ)^13 := by
    have hnat : (6379612457 : ℕ)^17*10000000000000^13 ≤ 5555600448233^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6379612457 10000000000 5555600448233 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1675359263/5000000000 : ℝ)^17 ≤ (5983655125893/25000000000000 : ℝ)^13 := by
    have hnat : (1675359263 : ℕ)^17*25000000000000^13 ≤ 5983655125893^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675359263 5000000000 5983655125893 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1488730127/5000000000 : ℝ), (-6379612457/10000000000 : ℝ), (1675359263/5000000000 : ℝ)] ![(20509375002357/100000000000000 : ℝ), (5555600448233/10000000000000 : ℝ), (5983655125893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1488730127/5000000000 : ℝ)|^17 ≤ (20509375002357/100000000000000 : ℝ)^13
        have hw : |(-1488730127/5000000000 : ℝ)|=(1488730127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6379612457/10000000000 : ℝ)|^17 ≤ (5555600448233/10000000000000 : ℝ)^13
        have hw : |(-6379612457/10000000000 : ℝ)|=(6379612457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1675359263/5000000000 : ℝ)|^17 ≤ (5983655125893/25000000000000 : ℝ)^13
        have hw : |(1675359263/5000000000 : ℝ)|=(1675359263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3623077113/5000000000 : ℝ)*x 0 + (252179193/1000000000 : ℝ)*x 1 + (2679833853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3623077113/5000000000 : ℝ)^17 ≤ (3281207941281/5000000000000 : ℝ)^13 := by
    have hnat : (3623077113 : ℕ)^17*5000000000000^13 ≤ 3281207941281^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3623077113 5000000000 3281207941281 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252179193/1000000000 : ℝ)^17 ≤ (825258096037/5000000000000 : ℝ)^13 := by
    have hnat : (252179193 : ℕ)^17*5000000000000^13 ≤ 825258096037^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252179193 1000000000 825258096037 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2679833853/10000000000 : ℝ)^17 ≤ (17870679230163/100000000000000 : ℝ)^13 := by
    have hnat : (2679833853 : ℕ)^17*100000000000000^13 ≤ 17870679230163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679833853 10000000000 17870679230163 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3623077113/5000000000 : ℝ), (252179193/1000000000 : ℝ), (2679833853/10000000000 : ℝ)] ![(3281207941281/5000000000000 : ℝ), (825258096037/5000000000000 : ℝ), (17870679230163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3623077113/5000000000 : ℝ)|^17 ≤ (3281207941281/5000000000000 : ℝ)^13
        have hw : |(3623077113/5000000000 : ℝ)|=(3623077113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252179193/1000000000 : ℝ)|^17 ≤ (825258096037/5000000000000 : ℝ)^13
        have hw : |(252179193/1000000000 : ℝ)|=(252179193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2679833853/10000000000 : ℝ)|^17 ≤ (17870679230163/100000000000000 : ℝ)^13
        have hw : |(2679833853/10000000000 : ℝ)|=(2679833853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1929704793/5000000000 : ℝ)*x 0 + (-4310029747/10000000000 : ℝ)*x 1 + (-2382858953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1929704793/5000000000 : ℝ)^17 ≤ (28793636911943/100000000000000 : ℝ)^13 := by
    have hnat : (1929704793 : ℕ)^17*100000000000000^13 ≤ 28793636911943^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929704793 5000000000 28793636911943 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310029747/10000000000 : ℝ)^17 ≤ (6653384977537/20000000000000 : ℝ)^13 := by
    have hnat : (4310029747 : ℕ)^17*20000000000000^13 ≤ 6653384977537^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310029747 10000000000 6653384977537 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2382858953/5000000000 : ℝ)^17 ≤ (37939438188173/100000000000000 : ℝ)^13 := by
    have hnat : (2382858953 : ℕ)^17*100000000000000^13 ≤ 37939438188173^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382858953 5000000000 37939438188173 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1929704793/5000000000 : ℝ), (-4310029747/10000000000 : ℝ), (-2382858953/5000000000 : ℝ)] ![(28793636911943/100000000000000 : ℝ), (6653384977537/20000000000000 : ℝ), (37939438188173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1929704793/5000000000 : ℝ)|^17 ≤ (28793636911943/100000000000000 : ℝ)^13
        have hw : |(1929704793/5000000000 : ℝ)|=(1929704793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4310029747/10000000000 : ℝ)|^17 ≤ (6653384977537/20000000000000 : ℝ)^13
        have hw : |(-4310029747/10000000000 : ℝ)|=(4310029747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2382858953/5000000000 : ℝ)|^17 ≤ (37939438188173/100000000000000 : ℝ)^13
        have hw : |(-2382858953/5000000000 : ℝ)|=(2382858953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (67896609/400000000 : ℝ)*x 0 + (-1821927859/10000000000 : ℝ)*x 1 + (8380832141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67896609/400000000 : ℝ)^17 ≤ (983557635617/10000000000000 : ℝ)^13 := by
    have hnat : (67896609 : ℕ)^17*10000000000000^13 ≤ 983557635617^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67896609 400000000 983557635617 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1821927859/10000000000 : ℝ)^17 ≤ (10789524560349/100000000000000 : ℝ)^13 := by
    have hnat : (1821927859 : ℕ)^17*100000000000000^13 ≤ 10789524560349^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821927859 10000000000 10789524560349 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8380832141/10000000000 : ℝ)^17 ≤ (79374899071501/100000000000000 : ℝ)^13 := by
    have hnat : (8380832141 : ℕ)^17*100000000000000^13 ≤ 79374899071501^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8380832141 10000000000 79374899071501 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67896609/400000000 : ℝ), (-1821927859/10000000000 : ℝ), (8380832141/10000000000 : ℝ)] ![(983557635617/10000000000000 : ℝ), (10789524560349/100000000000000 : ℝ), (79374899071501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67896609/400000000 : ℝ)|^17 ≤ (983557635617/10000000000000 : ℝ)^13
        have hw : |(67896609/400000000 : ℝ)|=(67896609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1821927859/10000000000 : ℝ)|^17 ≤ (10789524560349/100000000000000 : ℝ)^13
        have hw : |(-1821927859/10000000000 : ℝ)|=(1821927859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8380832141/10000000000 : ℝ)|^17 ≤ (79374899071501/100000000000000 : ℝ)^13
        have hw : |(8380832141/10000000000 : ℝ)|=(8380832141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-481268449/2500000000 : ℝ)*x 0 + (-1854457369/2500000000 : ℝ)*x 1 + (3003045749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481268449/2500000000 : ℝ)^17 ≤ (2898794008213/25000000000000 : ℝ)^13 := by
    have hnat : (481268449 : ℕ)^17*25000000000000^13 ≤ 2898794008213^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481268449 2500000000 2898794008213 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1854457369/2500000000 : ℝ)^17 ≤ (67664679419529/100000000000000 : ℝ)^13 := by
    have hnat : (1854457369 : ℕ)^17*100000000000000^13 ≤ 67664679419529^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854457369 2500000000 67664679419529 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3003045749/10000000000 : ℝ)^17 ≤ (20740144537443/100000000000000 : ℝ)^13 := by
    have hnat : (3003045749 : ℕ)^17*100000000000000^13 ≤ 20740144537443^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003045749 10000000000 20740144537443 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-481268449/2500000000 : ℝ), (-1854457369/2500000000 : ℝ), (3003045749/10000000000 : ℝ)] ![(2898794008213/25000000000000 : ℝ), (67664679419529/100000000000000 : ℝ), (20740144537443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-481268449/2500000000 : ℝ)|^17 ≤ (2898794008213/25000000000000 : ℝ)^13
        have hw : |(-481268449/2500000000 : ℝ)|=(481268449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1854457369/2500000000 : ℝ)|^17 ≤ (67664679419529/100000000000000 : ℝ)^13
        have hw : |(-1854457369/2500000000 : ℝ)|=(1854457369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3003045749/10000000000 : ℝ)|^17 ≤ (20740144537443/100000000000000 : ℝ)^13
        have hw : |(3003045749/10000000000 : ℝ)|=(3003045749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3575639271/5000000000 : ℝ)*x 0 + (2329318537/10000000000 : ℝ)*x 1 + (2989698169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3575639271/5000000000 : ℝ)^17 ≤ (64502816279509/100000000000000 : ℝ)^13 := by
    have hnat : (3575639271 : ℕ)^17*100000000000000^13 ≤ 64502816279509^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3575639271 5000000000 64502816279509 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2329318537/10000000000 : ℝ)^17 ≤ (1859688008111/12500000000000 : ℝ)^13 := by
    have hnat : (2329318537 : ℕ)^17*12500000000000^13 ≤ 1859688008111^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329318537 10000000000 1859688008111 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2989698169/10000000000 : ℝ)^17 ≤ (10309839814399/50000000000000 : ℝ)^13 := by
    have hnat : (2989698169 : ℕ)^17*50000000000000^13 ≤ 10309839814399^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2989698169 10000000000 10309839814399 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3575639271/5000000000 : ℝ), (2329318537/10000000000 : ℝ), (2989698169/10000000000 : ℝ)] ![(64502816279509/100000000000000 : ℝ), (1859688008111/12500000000000 : ℝ), (10309839814399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3575639271/5000000000 : ℝ)|^17 ≤ (64502816279509/100000000000000 : ℝ)^13
        have hw : |(3575639271/5000000000 : ℝ)|=(3575639271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2329318537/10000000000 : ℝ)|^17 ≤ (1859688008111/12500000000000 : ℝ)^13
        have hw : |(2329318537/10000000000 : ℝ)|=(2329318537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2989698169/10000000000 : ℝ)|^17 ≤ (10309839814399/50000000000000 : ℝ)^13
        have hw : |(2989698169/10000000000 : ℝ)|=(2989698169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (752999219/2500000000 : ℝ)*x 0 + (-3986114483/10000000000 : ℝ)*x 1 + (-5808430653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (752999219/2500000000 : ℝ)^17 ≤ (5205255712841/25000000000000 : ℝ)^13 := by
    have hnat : (752999219 : ℕ)^17*25000000000000^13 ≤ 5205255712841^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752999219 2500000000 5205255712841 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3986114483/10000000000 : ℝ)^17 ≤ (30035993653051/100000000000000 : ℝ)^13 := by
    have hnat : (3986114483 : ℕ)^17*100000000000000^13 ≤ 30035993653051^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3986114483 10000000000 30035993653051 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5808430653/10000000000 : ℝ)^17 ≤ (49142983478373/100000000000000 : ℝ)^13 := by
    have hnat : (5808430653 : ℕ)^17*100000000000000^13 ≤ 49142983478373^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5808430653 10000000000 49142983478373 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(752999219/2500000000 : ℝ), (-3986114483/10000000000 : ℝ), (-5808430653/10000000000 : ℝ)] ![(5205255712841/25000000000000 : ℝ), (30035993653051/100000000000000 : ℝ), (49142983478373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(752999219/2500000000 : ℝ)|^17 ≤ (5205255712841/25000000000000 : ℝ)^13
        have hw : |(752999219/2500000000 : ℝ)|=(752999219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3986114483/10000000000 : ℝ)|^17 ≤ (30035993653051/100000000000000 : ℝ)^13
        have hw : |(-3986114483/10000000000 : ℝ)|=(3986114483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5808430653/10000000000 : ℝ)|^17 ≤ (49142983478373/100000000000000 : ℝ)^13
        have hw : |(-5808430653/10000000000 : ℝ)|=(5808430653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304013_s1_s1_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (315474563/1000000000 : ℝ)*x 0 + (-255609469/1000000000 : ℝ)*x 1 + (6859227047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315474563/1000000000 : ℝ)^17 ≤ (22120733889413/100000000000000 : ℝ)^13 := by
    have hnat : (315474563 : ℕ)^17*100000000000000^13 ≤ 22120733889413^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315474563 1000000000 22120733889413 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255609469/1000000000 : ℝ)^17 ≤ (8399683524681/50000000000000 : ℝ)^13 := by
    have hnat : (255609469 : ℕ)^17*50000000000000^13 ≤ 8399683524681^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255609469 1000000000 8399683524681 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6859227047/10000000000 : ℝ)^17 ≤ (61079899043377/100000000000000 : ℝ)^13 := by
    have hnat : (6859227047 : ℕ)^17*100000000000000^13 ≤ 61079899043377^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6859227047 10000000000 61079899043377 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(315474563/1000000000 : ℝ), (-255609469/1000000000 : ℝ), (6859227047/10000000000 : ℝ)] ![(22120733889413/100000000000000 : ℝ), (8399683524681/50000000000000 : ℝ), (61079899043377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(315474563/1000000000 : ℝ)|^17 ≤ (22120733889413/100000000000000 : ℝ)^13
        have hw : |(315474563/1000000000 : ℝ)|=(315474563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-255609469/1000000000 : ℝ)|^17 ≤ (8399683524681/50000000000000 : ℝ)^13
        have hw : |(-255609469/1000000000 : ℝ)|=(255609469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6859227047/10000000000 : ℝ)|^17 ≤ (61079899043377/100000000000000 : ℝ)^13
        have hw : |(6859227047/10000000000 : ℝ)|=(6859227047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304013_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((18577/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18577/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-36249/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-36249/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65113/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65113/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((25259/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25259/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-24417/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-24417/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(738/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(738/3125 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (18577/25000 : ℝ) ^ (33/8 : ℝ) ≤ (14688983418857088671/50000000000000000000 : ℝ) := by
    have hpowers : (18577/25000 : ℝ)^33 ≤ (14688983418857088671/50000000000000000000 : ℝ)^8 := by
      have hnat : (18577 : ℕ)^33*50000000000000000000^8 ≤ 14688983418857088671^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18577 25000 14688983418857088671 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18577/25000 : ℝ)) (X := (14688983418857088671/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (64688983418857088671/50000000000000000000 : ℝ) ≤ (5322156710173513/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (64688983418857088671/50000000000000000000 : ℝ)^8 ≤ (5322156710173513/5000000000000000 : ℝ)^33 := by
      have hnat : (64688983418857088671 : ℕ)^8*5000000000000000^33 ≤ 5322156710173513^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64688983418857088671 50000000000000000000 5322156710173513 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5322156710173513/5000000000000000 : ℝ)) (X := (64688983418857088671/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (39688983418857088671/25000000000000000000 : ℝ) ≤ (11185665040644183/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (39688983418857088671/25000000000000000000 : ℝ)^8 ≤ (11185665040644183/10000000000000000 : ℝ)^33 := by
      have hnat : (39688983418857088671 : ℕ)^8*10000000000000000^33 ≤ 11185665040644183^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39688983418857088671 25000000000000000000 11185665040644183 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11185665040644183/10000000000000000 : ℝ)) (X := (39688983418857088671/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(322156710173513/3715400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(541351620297157/7430800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (18577/25000 : ℝ)) (alpha := (322156710173513/3715400000000000 : ℝ)) (beta := (541351620297157/7430800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18577/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(322156710173513/3715400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(541351620297157/7430800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (36249/50000 : ℝ) ^ (33/8 : ℝ) ≤ (6634143562272100843/25000000000000000000 : ℝ) := by
    have hpowers : (36249/50000 : ℝ)^33 ≤ (6634143562272100843/25000000000000000000 : ℝ)^8 := by
      have hnat : (36249 : ℕ)^33*25000000000000000000^8 ≤ 6634143562272100843^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36249 50000 6634143562272100843 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36249/50000 : ℝ)) (X := (6634143562272100843/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (31634143562272100843/25000000000000000000 : ℝ) ≤ (10587164326593961/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (31634143562272100843/25000000000000000000 : ℝ)^8 ≤ (10587164326593961/10000000000000000 : ℝ)^33 := by
      have hnat : (31634143562272100843 : ℕ)^8*10000000000000000^33 ≤ 10587164326593961^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31634143562272100843 25000000000000000000 10587164326593961 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10587164326593961/10000000000000000 : ℝ)) (X := (31634143562272100843/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (19134143562272100843/12500000000000000000 : ℝ) ≤ (2217450834143639/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (19134143562272100843/12500000000000000000 : ℝ)^8 ≤ (2217450834143639/2000000000000000 : ℝ)^33 := by
      have hnat : (19134143562272100843 : ℕ)^8*2000000000000000^33 ≤ 2217450834143639^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19134143562272100843 12500000000000000000 2217450834143639 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2217450834143639/2000000000000000 : ℝ)) (X := (19134143562272100843/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(195721442197987/2416600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(83348307354039/1208300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (36249/50000 : ℝ)) (alpha := (195721442197987/2416600000000000 : ℝ)) (beta := (83348307354039/1208300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (36249/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(195721442197987/2416600000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(83348307354039/1208300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (65113/100000 : ℝ) ^ (33/8 : ℝ) ≤ (4259114282084572773/25000000000000000000 : ℝ) := by
    have hpowers : (65113/100000 : ℝ)^33 ≤ (4259114282084572773/25000000000000000000 : ℝ)^8 := by
      have hnat : (65113 : ℕ)^33*25000000000000000000^8 ≤ 4259114282084572773^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65113 100000 4259114282084572773 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65113/100000 : ℝ)) (X := (4259114282084572773/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (29259114282084572773/25000000000000000000 : ℝ) ≤ (10388735927936579/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (29259114282084572773/25000000000000000000 : ℝ)^8 ≤ (10388735927936579/10000000000000000 : ℝ)^33 := by
      have hnat : (29259114282084572773 : ℕ)^8*10000000000000000^33 ≤ 10388735927936579^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29259114282084572773 25000000000000000000 10388735927936579 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10388735927936579/10000000000000000 : ℝ)) (X := (29259114282084572773/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (16759114282084572773/12500000000000000000 : ℝ) ≤ (5368346774074701/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (16759114282084572773/12500000000000000000 : ℝ)^8 ≤ (5368346774074701/5000000000000000 : ℝ)^33 := by
      have hnat : (16759114282084572773 : ℕ)^8*5000000000000000^33 ≤ 5368346774074701^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16759114282084572773 12500000000000000000 5368346774074701 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5368346774074701/5000000000000000 : ℝ)) (X := (16759114282084572773/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(388735927936579/6511300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(347957620212823/6511300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (65113/100000 : ℝ)) (alpha := (388735927936579/6511300000000000 : ℝ)) (beta := (347957620212823/6511300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (65113/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(388735927936579/6511300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(347957620212823/6511300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((3189020823/5000000000 : ℝ)*X 1 0+(1480516189/5000000000 : ℝ)*X 1 1+(1684223599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1010434999/2500000000 : ℝ)*X 2 0+(-507755791/1250000000 : ℝ)*X 2 1+(-2415875663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3034623353/10000000000 : ℝ)*X 0 0+(-2875028479/10000000000 : ℝ)*X 0 1+(1678246503/2500000000 : ℝ)*X 0 2+(3034623353/10000000000 : ℝ)*X 1 0+(-2875028479/10000000000 : ℝ)*X 1 1+(1678246503/2500000000 : ℝ)*X 1 2+(3034623353/10000000000 : ℝ)*X 2 0+(-2875028479/10000000000 : ℝ)*X 2 1+(1678246503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2490295939/10000000000 : ℝ)*X 0 0+(-7229745329/10000000000 : ℝ)*X 0 1+(1366401519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((6349286639/10000000000 : ℝ)*X 1 0+(3030119391/10000000000 : ℝ)*X 1 1+(1668367973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1032378913/2500000000 : ℝ)*X 2 0+(-2009878793/5000000000 : ℝ)*X 2 1+(-2394178441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1166521571/5000000000 : ℝ)*X 0 0+(-1285451439/10000000000 : ℝ)*X 0 1+(8290140139/10000000000 : ℝ)*X 0 2+(1166521571/5000000000 : ℝ)*X 1 0+(-1285451439/10000000000 : ℝ)*X 1 1+(8290140139/10000000000 : ℝ)*X 1 2+(1166521571/5000000000 : ℝ)*X 2 0+(-1285451439/10000000000 : ℝ)*X 2 1+(8290140139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1488730127/5000000000 : ℝ)*X 0 0+(-6379612457/10000000000 : ℝ)*X 0 1+(1675359263/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3623077113/5000000000 : ℝ)*X 1 0+(252179193/1000000000 : ℝ)*X 1 1+(2679833853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1929704793/5000000000 : ℝ)*X 2 0+(-4310029747/10000000000 : ℝ)*X 2 1+(-2382858953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((67896609/400000000 : ℝ)*X 0 0+(-1821927859/10000000000 : ℝ)*X 0 1+(8380832141/10000000000 : ℝ)*X 0 2+(67896609/400000000 : ℝ)*X 1 0+(-1821927859/10000000000 : ℝ)*X 1 1+(8380832141/10000000000 : ℝ)*X 1 2+(67896609/400000000 : ℝ)*X 2 0+(-1821927859/10000000000 : ℝ)*X 2 1+(8380832141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-481268449/2500000000 : ℝ)*X 0 0+(-1854457369/2500000000 : ℝ)*X 0 1+(3003045749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3575639271/5000000000 : ℝ)*X 1 0+(2329318537/10000000000 : ℝ)*X 1 1+(2989698169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((752999219/2500000000 : ℝ)*X 2 0+(-3986114483/10000000000 : ℝ)*X 2 1+(-5808430653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((315474563/1000000000 : ℝ)*X 0 0+(-255609469/1000000000 : ℝ)*X 0 1+(6859227047/10000000000 : ℝ)*X 0 2+(315474563/1000000000 : ℝ)*X 1 0+(-255609469/1000000000 : ℝ)*X 1 1+(6859227047/10000000000 : ℝ)*X 1 2+(315474563/1000000000 : ℝ)*X 2 0+(-255609469/1000000000 : ℝ)*X 2 1+(6859227047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304013_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((25259/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25259/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (109815033093899851960497139077/9134779725426875000000000000000000 : ℝ) := by norm_num
    linear_combination (22038389881/1000000000000 : ℝ)*(base3) + (310803223/800000000 : ℝ)*(base40) + (1079001/200000000000 : ℝ)*(base49) + (38236356227/50000000000 : ℝ)*(base50) + (956900874913/200000000000 : ℝ)*(major_s1_0) + (956900874913/200000000000 : ℝ)*(major_s1_1) + (956900874913/200000000000 : ℝ)*(major_s1_2) + (6414493014029/1000000000000 : ℝ)*(sp_s1_7) + (6436535790579/1000000000000 : ℝ)*(sp_s1_8) + (400894449911/62500000000 : ℝ)*(sp_s1_9) + (3132437675929/1000000000000 : ℝ)*(sp_s1_13) + (93101061/500000000000 : ℝ)*(sp_s1_16) + (7818851/250000000000 : ℝ)*(sp_s1_20) + (4386669/1000000000000 : ℝ)*(sp_s1_21) + (3154507341213/1000000000000 : ℝ)*(f.failure) + (3207248700349/500000000000 : ℝ)*(f.sum) + (12433423389382337229/31470415160000000000000000000000 : ℝ)*base62 + (255799763914847/1302260000000000000000000000 : ℝ)*base64 + (118762541718541/241660000000000000000000000 : ℝ)*base66 + (133851078035947/1302260000000000000000000000 : ℝ)*base68 + (15409291675309028437/48384168040000000000000000000000 : ℝ)*base70 + (11044192903677/1486160000000000000000000000 : ℝ)*base73 + (17826078277263/96664000000000000000000000 : ℝ)*base74 + (64988262804247/148616000000000000000000000 : ℝ)*base76 + (8063480025356725709/17957271280000000000000000000000 : ℝ)*base78 + (5233/12500000000000000 : ℝ)*base86 + (5233/12500000000000000 : ℝ)*base88 + (5233/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-24417/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-24417/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24657466194495301809897/3255650000000000000000000000 : ℝ) := by norm_num
    linear_combination (2391497/1000000000000 : ℝ)*(base39) + (723705601039/1000000000000 : ℝ)*(base40) + (302015625699/1000000000000 : ℝ)*(base50) + (989827/1000000000000 : ℝ)*(base59) + (53242243309/500000000000 : ℝ)*(base60) + (4494807555789/1000000000000 : ℝ)*(major_s1_0) + (4494807555789/1000000000000 : ℝ)*(major_s1_1) + (4494807555789/1000000000000 : ℝ)*(major_s1_2) + (221438043/1000000000000 : ℝ)*(sp_s1_2) + (6026107420717/1000000000000 : ℝ)*(sp_s1_14) + (6026066546547/1000000000000 : ℝ)*(sp_s1_15) + (3012942991337/500000000000 : ℝ)*(sp_s1_16) + (2963505166273/1000000000000 : ℝ)*(sp_s1_20) + (40874171/1000000000000 : ℝ)*(sp_s1_22) + (2963505166273/1000000000000 : ℝ)*(f.failure) + (6026107420717/1000000000000 : ℝ)*(f.sum) + (51172063197209862073/157352075800000000000000000000000 : ℝ)*base62 + (5447202923853467/6511300000000000000000000000 : ℝ)*base64 + (114664186635279/1208300000000000000000000000 : ℝ)*base66 + (8345967784627939/6511300000000000000000000000 : ℝ)*base68 + (252094331329558022497/241920840200000000000000000000000 : ℝ)*base70 + (2692800521095767/7430800000000000000000000000 : ℝ)*base72 + (347151245143037/2416600000000000000000000000 : ℝ)*base75 + (582293525543817/3715400000000000000000000000 : ℝ)*base77 + (15187182506680464087/89786356400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (7307/12500000000000000 : ℝ)*base87 + (7307/12500000000000000 : ℝ)*base89 + (7307/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(738/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(738/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (82084407249623015512036059/22446589100000000000000000000000 : ℝ) := by norm_num
    linear_combination (1539969175117/1000000000000 : ℝ)*(base3) + (1149222937747/1000000000000 : ℝ)*(base40) + (794644440521/500000000000 : ℝ)*(base50) + (1796018615897/500000000000 : ℝ)*(major_s1_0) + (1796018615897/500000000000 : ℝ)*(major_s1_1) + (1796018615897/500000000000 : ℝ)*(major_s1_2) + (318561/500000000000 : ℝ)*(sp_s1_1) + (3756339/1000000000000 : ℝ)*(sp_s1_2) + (3555401/100000000000 : ℝ)*(sp_s1_6) + (2823483/200000000000 : ℝ)*(sp_s1_16) + (963156065693/200000000000 : ℝ)*(sp_s1_21) + (317787443323/50000000000 : ℝ)*(sp_s1_22) + (481576245471/100000000000 : ℝ)*(sp_s1_23) + (828288187031/1000000000000 : ℝ)*(sp_s1_27) + (2368292916157/1000000000000 : ℝ)*(f.failure) + (963156065693/200000000000 : ℝ)*(f.sum) + (10745080264922421151/78676037900000000000000000000000 : ℝ)*base63 + (2406688947496569/3255650000000000000000000000 : ℝ)*base65 + (320895715719747/604150000000000000000000000 : ℝ)*base66 + (2744093174572117/3255650000000000000000000000 : ℝ)*base68 + (50079201081042010941/120960420100000000000000000000000 : ℝ)*base70 + (1472461299373591/3715400000000000000000000000 : ℝ)*base72 + (408385811841/1208300000000000000000000000 : ℝ)*base75 + (416819372372449/1857700000000000000000000000 : ℝ)*base76 + (2760315155104764689/44893178200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (4437/12500000000000000 : ℝ)*base86 + (4437/12500000000000000 : ℝ)*base88 + (4437/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((18577/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18577/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-36249/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-36249/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65113/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65113/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((25259/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25259/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-24417/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-24417/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(738/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(738/3125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304013_s1 p hpa hpb X hX hprev0

#print axioms solution
