-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:58:51.151641+00:00
-- url     : https://prove2.me/submissions/64d4768e-fa45-4cd3-95ae-48e8562123e7

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
theorem collision_support_c303062_s1_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-466080199/5000000000 : ℝ)*x 0 + (63441871/125000000 : ℝ)*x 1 + (-6338972877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466080199/5000000000 : ℝ)^33 ≤ (545302726137/12500000000000 : ℝ)^25 := by
    have hnat : (466080199 : ℕ)^33*12500000000000^25 ≤ 545302726137^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466080199 5000000000 545302726137 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63441871/125000000 : ℝ)^33 ≤ (40852165227999/100000000000000 : ℝ)^25 := by
    have hnat : (63441871 : ℕ)^33*100000000000000^25 ≤ 40852165227999^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63441871 125000000 40852165227999 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6338972877/10000000000 : ℝ)^33 ≤ (54785412940997/100000000000000 : ℝ)^25 := by
    have hnat : (6338972877 : ℕ)^33*100000000000000^25 ≤ 54785412940997^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6338972877 10000000000 54785412940997 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466080199/5000000000 : ℝ), (63441871/125000000 : ℝ), (-6338972877/10000000000 : ℝ)] ![(545302726137/12500000000000 : ℝ), (40852165227999/100000000000000 : ℝ), (54785412940997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466080199/5000000000 : ℝ)|^33 ≤ (545302726137/12500000000000 : ℝ)^25
        have hw : |(-466080199/5000000000 : ℝ)|=(466080199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63441871/125000000 : ℝ)|^33 ≤ (40852165227999/100000000000000 : ℝ)^25
        have hw : |(63441871/125000000 : ℝ)|=(63441871/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6338972877/10000000000 : ℝ)|^33 ≤ (54785412940997/100000000000000 : ℝ)^25
        have hw : |(-6338972877/10000000000 : ℝ)|=(6338972877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (509670227/1000000000 : ℝ)*x 0 + (-460663689/5000000000 : ℝ)*x 1 + (-3162461639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509670227/1000000000 : ℝ)^33 ≤ (41079185984481/100000000000000 : ℝ)^25 := by
    have hnat : (509670227 : ℕ)^33*100000000000000^25 ≤ 41079185984481^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509670227 1000000000 41079185984481 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460663689/5000000000 : ℝ)^33 ≤ (214781293563/5000000000000 : ℝ)^25 := by
    have hnat : (460663689 : ℕ)^33*5000000000000^25 ≤ 214781293563^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460663689 5000000000 214781293563 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3162461639/5000000000 : ℝ)^33 ≤ (2731259406073/5000000000000 : ℝ)^25 := by
    have hnat : (3162461639 : ℕ)^33*5000000000000^25 ≤ 2731259406073^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3162461639 5000000000 2731259406073 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(509670227/1000000000 : ℝ), (-460663689/5000000000 : ℝ), (-3162461639/5000000000 : ℝ)] ![(41079185984481/100000000000000 : ℝ), (214781293563/5000000000000 : ℝ), (2731259406073/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(509670227/1000000000 : ℝ)|^33 ≤ (41079185984481/100000000000000 : ℝ)^25
        have hw : |(509670227/1000000000 : ℝ)|=(509670227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-460663689/5000000000 : ℝ)|^33 ≤ (214781293563/5000000000000 : ℝ)^25
        have hw : |(-460663689/5000000000 : ℝ)|=(460663689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3162461639/5000000000 : ℝ)|^33 ≤ (2731259406073/5000000000000 : ℝ)^25
        have hw : |(-3162461639/5000000000 : ℝ)|=(3162461639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-315386893/2500000000 : ℝ)*x 0 + (1985154159/10000000000 : ℝ)*x 1 + (-2144334347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315386893/2500000000 : ℝ)^33 ≤ (6504183634813/100000000000000 : ℝ)^25 := by
    have hnat : (315386893 : ℕ)^33*100000000000000^25 ≤ 6504183634813^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315386893 2500000000 6504183634813 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1985154159/10000000000 : ℝ)^33 ≤ (11832823705117/100000000000000 : ℝ)^25 := by
    have hnat : (1985154159 : ℕ)^33*100000000000000^25 ≤ 11832823705117^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985154159 10000000000 11832823705117 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144334347/2500000000 : ℝ)^33 ≤ (40831496323433/50000000000000 : ℝ)^25 := by
    have hnat : (2144334347 : ℕ)^33*50000000000000^25 ≤ 40831496323433^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144334347 2500000000 40831496323433 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315386893/2500000000 : ℝ), (1985154159/10000000000 : ℝ), (-2144334347/2500000000 : ℝ)] ![(6504183634813/100000000000000 : ℝ), (11832823705117/100000000000000 : ℝ), (40831496323433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315386893/2500000000 : ℝ)|^33 ≤ (6504183634813/100000000000000 : ℝ)^25
        have hw : |(-315386893/2500000000 : ℝ)|=(315386893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1985154159/10000000000 : ℝ)|^33 ≤ (11832823705117/100000000000000 : ℝ)^25
        have hw : |(1985154159/10000000000 : ℝ)|=(1985154159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144334347/2500000000 : ℝ)|^33 ≤ (40831496323433/50000000000000 : ℝ)^25
        have hw : |(-2144334347/2500000000 : ℝ)|=(2144334347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (291577929/1250000000 : ℝ)*x 0 + (-431012067/5000000000 : ℝ)*x 1 + (-4279199463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291577929/1250000000 : ℝ)^33 ≤ (14640466554713/100000000000000 : ℝ)^25 := by
    have hnat : (291577929 : ℕ)^33*100000000000000^25 ≤ 14640466554713^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291577929 1250000000 14640466554713 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431012067/5000000000 : ℝ)^33 ≤ (3934464588411/100000000000000 : ℝ)^25 := by
    have hnat : (431012067 : ℕ)^33*100000000000000^25 ≤ 3934464588411^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431012067 5000000000 3934464588411 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4279199463/5000000000 : ℝ)^33 ≤ (40712534418161/50000000000000 : ℝ)^25 := by
    have hnat : (4279199463 : ℕ)^33*50000000000000^25 ≤ 40712534418161^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279199463 5000000000 40712534418161 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(291577929/1250000000 : ℝ), (-431012067/5000000000 : ℝ), (-4279199463/5000000000 : ℝ)] ![(14640466554713/100000000000000 : ℝ), (3934464588411/100000000000000 : ℝ), (40712534418161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(291577929/1250000000 : ℝ)|^33 ≤ (14640466554713/100000000000000 : ℝ)^25
        have hw : |(291577929/1250000000 : ℝ)|=(291577929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431012067/5000000000 : ℝ)|^33 ≤ (3934464588411/100000000000000 : ℝ)^25
        have hw : |(-431012067/5000000000 : ℝ)|=(431012067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4279199463/5000000000 : ℝ)|^33 ≤ (40712534418161/50000000000000 : ℝ)^25
        have hw : |(-4279199463/5000000000 : ℝ)|=(4279199463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2629979217/10000000000 : ℝ)*x 0 + (76233219/100000000 : ℝ)*x 1 + (2126155739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629979217/10000000000 : ℝ)^33 ≤ (1715288033639/10000000000000 : ℝ)^25 := by
    have hnat : (2629979217 : ℕ)^33*10000000000000^25 ≤ 1715288033639^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629979217 10000000000 1715288033639 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76233219/100000000 : ℝ)^33 ≤ (69892475239969/100000000000000 : ℝ)^25 := by
    have hnat : (76233219 : ℕ)^33*100000000000000^25 ≤ 69892475239969^25*100000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76233219 100000000 69892475239969 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126155739/10000000000 : ℝ)^33 ≤ (12954644404029/100000000000000 : ℝ)^25 := by
    have hnat : (2126155739 : ℕ)^33*100000000000000^25 ≤ 12954644404029^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126155739 10000000000 12954644404029 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629979217/10000000000 : ℝ), (76233219/100000000 : ℝ), (2126155739/10000000000 : ℝ)] ![(1715288033639/10000000000000 : ℝ), (69892475239969/100000000000000 : ℝ), (12954644404029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629979217/10000000000 : ℝ)|^33 ≤ (1715288033639/10000000000000 : ℝ)^25
        have hw : |(2629979217/10000000000 : ℝ)|=(2629979217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(76233219/100000000 : ℝ)|^33 ≤ (69892475239969/100000000000000 : ℝ)^25
        have hw : |(76233219/100000000 : ℝ)|=(76233219/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126155739/10000000000 : ℝ)|^33 ≤ (12954644404029/100000000000000 : ℝ)^25
        have hw : |(2126155739/10000000000 : ℝ)|=(2126155739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (730160253/2000000000 : ℝ)*x 0 + (61906501/78125000 : ℝ)*x 1 + (-1/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730160253/2000000000 : ℝ)^33 ≤ (5289107688781/20000000000000 : ℝ)^25 := by
    have hnat : (730160253 : ℕ)^33*20000000000000^25 ≤ 5289107688781^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730160253 2000000000 5289107688781 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61906501/78125000 : ℝ)^33 ≤ (73554461546309/100000000000000 : ℝ)^25 := by
    have hnat : (61906501 : ℕ)^33*100000000000000^25 ≤ 73554461546309^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61906501 78125000 73554461546309 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1/2000000000 : ℝ)^33 ≤ (53/100000000000000 : ℝ)^25 := by
    have hnat : (1 : ℕ)^33*100000000000000^25 ≤ 53^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 2000000000 53 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(730160253/2000000000 : ℝ), (61906501/78125000 : ℝ), (-1/2000000000 : ℝ)] ![(5289107688781/20000000000000 : ℝ), (73554461546309/100000000000000 : ℝ), (53/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(730160253/2000000000 : ℝ)|^33 ≤ (5289107688781/20000000000000 : ℝ)^25
        have hw : |(730160253/2000000000 : ℝ)|=(730160253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(61906501/78125000 : ℝ)|^33 ≤ (73554461546309/100000000000000 : ℝ)^25
        have hw : |(61906501/78125000 : ℝ)|=(61906501/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1/2000000000 : ℝ)|^33 ≤ (53/100000000000000 : ℝ)^25
        have hw : |(-1/2000000000 : ℝ)|=(1/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-49485119/500000000 : ℝ)*x 0 + (2150842971/10000000000 : ℝ)*x 1 + (-4307040651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49485119/500000000 : ℝ)^33 ≤ (1180337214277/25000000000000 : ℝ)^25 := by
    have hnat : (49485119 : ℕ)^33*25000000000000^25 ≤ 1180337214277^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49485119 500000000 1180337214277 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150842971/10000000000 : ℝ)^33 ≤ (13153565445507/100000000000000 : ℝ)^25 := by
    have hnat : (2150842971 : ℕ)^33*100000000000000^25 ≤ 13153565445507^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150842971 10000000000 13153565445507 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4307040651/5000000000 : ℝ)^33 ≤ (8212508568571/10000000000000 : ℝ)^25 := by
    have hnat : (4307040651 : ℕ)^33*10000000000000^25 ≤ 8212508568571^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307040651 5000000000 8212508568571 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49485119/500000000 : ℝ), (2150842971/10000000000 : ℝ), (-4307040651/5000000000 : ℝ)] ![(1180337214277/25000000000000 : ℝ), (13153565445507/100000000000000 : ℝ), (8212508568571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49485119/500000000 : ℝ)|^33 ≤ (1180337214277/25000000000000 : ℝ)^25
        have hw : |(-49485119/500000000 : ℝ)|=(49485119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2150842971/10000000000 : ℝ)|^33 ≤ (13153565445507/100000000000000 : ℝ)^25
        have hw : |(2150842971/10000000000 : ℝ)|=(2150842971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4307040651/5000000000 : ℝ)|^33 ≤ (8212508568571/10000000000000 : ℝ)^25
        have hw : |(-4307040651/5000000000 : ℝ)|=(4307040651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1848168549/10000000000 : ℝ)*x 0 + (-691776571/5000000000 : ℝ)*x 1 + (-8595062141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1848168549/10000000000 : ℝ)^33 ≤ (5383551647959/50000000000000 : ℝ)^25 := by
    have hnat : (1848168549 : ℕ)^33*50000000000000^25 ≤ 5383551647959^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848168549 10000000000 5383551647959 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (691776571/5000000000 : ℝ)^33 ≤ (293883028517/4000000000000 : ℝ)^25 := by
    have hnat : (691776571 : ℕ)^33*4000000000000^25 ≤ 293883028517^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691776571 5000000000 293883028517 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8595062141/10000000000 : ℝ)^33 ≤ (81885820985667/100000000000000 : ℝ)^25 := by
    have hnat : (8595062141 : ℕ)^33*100000000000000^25 ≤ 81885820985667^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8595062141 10000000000 81885820985667 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1848168549/10000000000 : ℝ), (-691776571/5000000000 : ℝ), (-8595062141/10000000000 : ℝ)] ![(5383551647959/50000000000000 : ℝ), (293883028517/4000000000000 : ℝ), (81885820985667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1848168549/10000000000 : ℝ)|^33 ≤ (5383551647959/50000000000000 : ℝ)^25
        have hw : |(1848168549/10000000000 : ℝ)|=(1848168549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-691776571/5000000000 : ℝ)|^33 ≤ (293883028517/4000000000000 : ℝ)^25
        have hw : |(-691776571/5000000000 : ℝ)|=(691776571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8595062141/10000000000 : ℝ)|^33 ≤ (81885820985667/100000000000000 : ℝ)^25
        have hw : |(-8595062141/10000000000 : ℝ)|=(8595062141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3681449171/5000000000 : ℝ)*x 0 + (585781441/2000000000 : ℝ)*x 1 + (2189903373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3681449171/5000000000 : ℝ)^33 ≤ (66758169777927/100000000000000 : ℝ)^25 := by
    have hnat : (3681449171 : ℕ)^33*100000000000000^25 ≤ 66758169777927^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681449171 5000000000 66758169777927 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585781441/2000000000 : ℝ)^33 ≤ (790881468789/4000000000000 : ℝ)^25 := by
    have hnat : (585781441 : ℕ)^33*4000000000000^25 ≤ 790881468789^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585781441 2000000000 790881468789 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189903373/10000000000 : ℝ)^33 ≤ (841862092851/6250000000000 : ℝ)^25 := by
    have hnat : (2189903373 : ℕ)^33*6250000000000^25 ≤ 841862092851^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189903373 10000000000 841862092851 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3681449171/5000000000 : ℝ), (585781441/2000000000 : ℝ), (2189903373/10000000000 : ℝ)] ![(66758169777927/100000000000000 : ℝ), (790881468789/4000000000000 : ℝ), (841862092851/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3681449171/5000000000 : ℝ)|^33 ≤ (66758169777927/100000000000000 : ℝ)^25
        have hw : |(3681449171/5000000000 : ℝ)|=(3681449171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(585781441/2000000000 : ℝ)|^33 ≤ (790881468789/4000000000000 : ℝ)^25
        have hw : |(585781441/2000000000 : ℝ)|=(585781441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2189903373/10000000000 : ℝ)|^33 ≤ (841862092851/6250000000000 : ℝ)^25
        have hw : |(2189903373/10000000000 : ℝ)|=(2189903373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8150839259/10000000000 : ℝ)*x 0 + (134197173/400000000 : ℝ)*x 1 + (287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8150839259/10000000000 : ℝ)^33 ≤ (9543267266541/12500000000000 : ℝ)^25 := by
    have hnat : (8150839259 : ℕ)^33*12500000000000^25 ≤ 9543267266541^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8150839259 10000000000 9543267266541 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134197173/400000000 : ℝ)^33 ≤ (4730772369919/20000000000000 : ℝ)^25 := by
    have hnat : (134197173 : ℕ)^33*20000000000000^25 ≤ 4730772369919^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134197173 400000000 4730772369919 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287/10000000000 : ℝ)^33 ≤ (11077/100000000000000 : ℝ)^25 := by
    have hnat : (287 : ℕ)^33*100000000000000^25 ≤ 11077^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287 10000000000 11077 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8150839259/10000000000 : ℝ), (134197173/400000000 : ℝ), (287/10000000000 : ℝ)] ![(9543267266541/12500000000000 : ℝ), (4730772369919/20000000000000 : ℝ), (11077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8150839259/10000000000 : ℝ)|^33 ≤ (9543267266541/12500000000000 : ℝ)^25
        have hw : |(8150839259/10000000000 : ℝ)|=(8150839259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134197173/400000000 : ℝ)|^33 ≤ (4730772369919/20000000000000 : ℝ)^25
        have hw : |(134197173/400000000 : ℝ)|=(134197173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287/10000000000 : ℝ)|^33 ≤ (11077/100000000000000 : ℝ)^25
        have hw : |(287/10000000000 : ℝ)|=(287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-406647043/10000000000 : ℝ)*x 0 + (889134377/1250000000 : ℝ)*x 1 + (-224525483/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406647043/10000000000 : ℝ)^33 ≤ (1459376190609/100000000000000 : ℝ)^25 := by
    have hnat : (406647043 : ℕ)^33*100000000000000^25 ≤ 1459376190609^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406647043 10000000000 1459376190609 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (889134377/1250000000 : ℝ)^33 ≤ (7973073475531/12500000000000 : ℝ)^25 := by
    have hnat : (889134377 : ℕ)^33*12500000000000^25 ≤ 7973073475531^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889134377 1250000000 7973073475531 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224525483/500000000 : ℝ)^33 ≤ (8689008995733/25000000000000 : ℝ)^25 := by
    have hnat : (224525483 : ℕ)^33*25000000000000^25 ≤ 8689008995733^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224525483 500000000 8689008995733 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406647043/10000000000 : ℝ), (889134377/1250000000 : ℝ), (-224525483/500000000 : ℝ)] ![(1459376190609/100000000000000 : ℝ), (7973073475531/12500000000000 : ℝ), (8689008995733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406647043/10000000000 : ℝ)|^33 ≤ (1459376190609/100000000000000 : ℝ)^25
        have hw : |(-406647043/10000000000 : ℝ)|=(406647043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(889134377/1250000000 : ℝ)|^33 ≤ (7973073475531/12500000000000 : ℝ)^25
        have hw : |(889134377/1250000000 : ℝ)|=(889134377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224525483/500000000 : ℝ)|^33 ≤ (8689008995733/25000000000000 : ℝ)^25
        have hw : |(-224525483/500000000 : ℝ)|=(224525483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (94173953/125000000 : ℝ)*x 0 + (-18985757/400000000 : ℝ)*x 1 + (-791109947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94173953/125000000 : ℝ)^33 ≤ (68812516355041/100000000000000 : ℝ)^25 := by
    have hnat : (94173953 : ℕ)^33*100000000000000^25 ≤ 68812516355041^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94173953 125000000 68812516355041 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18985757/400000000 : ℝ)^33 ≤ (894902389193/50000000000000 : ℝ)^25 := by
    have hnat : (18985757 : ℕ)^33*50000000000000^25 ≤ 894902389193^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18985757 400000000 894902389193 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791109947/2000000000 : ℝ)^33 ≤ (7349419714047/25000000000000 : ℝ)^25 := by
    have hnat : (791109947 : ℕ)^33*25000000000000^25 ≤ 7349419714047^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791109947 2000000000 7349419714047 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(94173953/125000000 : ℝ), (-18985757/400000000 : ℝ), (-791109947/2000000000 : ℝ)] ![(68812516355041/100000000000000 : ℝ), (894902389193/50000000000000 : ℝ), (7349419714047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(94173953/125000000 : ℝ)|^33 ≤ (68812516355041/100000000000000 : ℝ)^25
        have hw : |(94173953/125000000 : ℝ)|=(94173953/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18985757/400000000 : ℝ)|^33 ≤ (894902389193/50000000000000 : ℝ)^25
        have hw : |(-18985757/400000000 : ℝ)|=(18985757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-791109947/2000000000 : ℝ)|^33 ≤ (7349419714047/25000000000000 : ℝ)^25
        have hw : |(-791109947/2000000000 : ℝ)|=(791109947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2297462781/10000000000 : ℝ)*x 0 + (477708723/625000000 : ℝ)*x 1 + (2437470979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2297462781/10000000000 : ℝ)^33 ≤ (14349871086943/100000000000000 : ℝ)^25 := by
    have hnat : (2297462781 : ℕ)^33*100000000000000^25 ≤ 14349871086943^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297462781 10000000000 14349871086943 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477708723/625000000 : ℝ)^33 ≤ (35067416210309/50000000000000 : ℝ)^25 := by
    have hnat : (477708723 : ℕ)^33*50000000000000^25 ≤ 35067416210309^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477708723 625000000 35067416210309 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2437470979/10000000000 : ℝ)^33 ≤ (7757648237847/50000000000000 : ℝ)^25 := by
    have hnat : (2437470979 : ℕ)^33*50000000000000^25 ≤ 7757648237847^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437470979 10000000000 7757648237847 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2297462781/10000000000 : ℝ), (477708723/625000000 : ℝ), (2437470979/10000000000 : ℝ)] ![(14349871086943/100000000000000 : ℝ), (35067416210309/50000000000000 : ℝ), (7757648237847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2297462781/10000000000 : ℝ)|^33 ≤ (14349871086943/100000000000000 : ℝ)^25
        have hw : |(2297462781/10000000000 : ℝ)|=(2297462781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(477708723/625000000 : ℝ)|^33 ≤ (35067416210309/50000000000000 : ℝ)^25
        have hw : |(477708723/625000000 : ℝ)|=(477708723/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2437470979/10000000000 : ℝ)|^33 ≤ (7757648237847/50000000000000 : ℝ)^25
        have hw : |(2437470979/10000000000 : ℝ)|=(2437470979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s1_s1_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8408226657/10000000000 : ℝ)*x 0 + (597739073/2000000000 : ℝ)*x 1 + (-18050003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8408226657/10000000000 : ℝ)^33 ≤ (79544438689273/100000000000000 : ℝ)^25 := by
    have hnat : (8408226657 : ℕ)^33*100000000000000^25 ≤ 79544438689273^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8408226657 10000000000 79544438689273 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597739073/2000000000 : ℝ)^33 ≤ (507663321303/2500000000000 : ℝ)^25 := by
    have hnat : (597739073 : ℕ)^33*2500000000000^25 ≤ 507663321303^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597739073 2000000000 507663321303 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18050003/2500000000 : ℝ)^33 ≤ (9314278373/6250000000000 : ℝ)^25 := by
    have hnat : (18050003 : ℕ)^33*6250000000000^25 ≤ 9314278373^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18050003 2500000000 9314278373 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8408226657/10000000000 : ℝ), (597739073/2000000000 : ℝ), (-18050003/2500000000 : ℝ)] ![(79544438689273/100000000000000 : ℝ), (507663321303/2500000000000 : ℝ), (9314278373/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8408226657/10000000000 : ℝ)|^33 ≤ (79544438689273/100000000000000 : ℝ)^25
        have hw : |(8408226657/10000000000 : ℝ)|=(8408226657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597739073/2000000000 : ℝ)|^33 ≤ (507663321303/2500000000000 : ℝ)^25
        have hw : |(597739073/2000000000 : ℝ)|=(597739073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18050003/2500000000 : ℝ)|^33 ≤ (9314278373/6250000000000 : ℝ)^25
        have hw : |(-18050003/2500000000 : ℝ)|=(18050003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303062_s1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((9499/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9499/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93867/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(93867/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5197/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5197/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((86563/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86563/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43049/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43049/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-71347/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-71347/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (91389/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (9499/10000 : ℝ) ^ (131/32 : ℝ) ≤ (81024965104741188503/100000000000000000000 : ℝ) := by
    have hpowers : (9499/10000 : ℝ)^131 ≤ (81024965104741188503/100000000000000000000 : ℝ)^32 := by
      have hnat : (9499 : ℕ)^131*100000000000000000000^32 ≤ 81024965104741188503^32*10000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9499 10000 81024965104741188503 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9499/10000 : ℝ)) (X := (81024965104741188503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (181024965104741188503/100000000000000000000 : ℝ) ≤ (90312745817121/78125000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (181024965104741188503/100000000000000000000 : ℝ)^32 ≤ (90312745817121/78125000000000 : ℝ)^131 := by
      have hnat : (181024965104741188503 : ℕ)^32*78125000000000^131 ≤ 90312745817121^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        181024965104741188503 100000000000000000000 90312745817121 78125000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (90312745817121/78125000000000 : ℝ)) (X := (181024965104741188503/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (131024965104741188503/50000000000000000000 : ℝ) ≤ (101225672464563/80000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (131024965104741188503/50000000000000000000 : ℝ)^32 ≤ (101225672464563/80000000000000 : ℝ)^131 := by
      have hnat : (131024965104741188503 : ℕ)^32*80000000000000^131 ≤ 101225672464563^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131024965104741188503 50000000000000000000 101225672464563 80000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (101225672464563/80000000000000 : ℝ)) (X := (131024965104741188503/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1741106545303/10601562500000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(156168227639841/1357000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (9499/10000 : ℝ)) (alpha := (1741106545303/10601562500000 : ℝ)) (beta := (156168227639841/1357000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9499/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1741106545303/10601562500000 : ℝ)*((1 : ℝ)*pair X 0 1)+(156168227639841/1357000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (93867/100000 : ℝ) ^ (131/32 : ℝ) ≤ (3858734022210698859/5000000000000000000 : ℝ) := by
    have hpowers : (93867/100000 : ℝ)^131 ≤ (3858734022210698859/5000000000000000000 : ℝ)^32 := by
      have hnat : (93867 : ℕ)^131*5000000000000000000^32 ≤ 3858734022210698859^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93867 100000 3858734022210698859 5000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93867/100000 : ℝ)) (X := (3858734022210698859/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (8858734022210698859/5000000000000000000 : ℝ) ≤ (91995853851287/80000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (8858734022210698859/5000000000000000000 : ℝ)^32 ≤ (91995853851287/80000000000000 : ℝ)^131 := by
      have hnat : (8858734022210698859 : ℕ)^32*80000000000000^131 ≤ 91995853851287^131*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8858734022210698859 5000000000000000000 91995853851287 80000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (91995853851287/80000000000000 : ℝ)) (X := (8858734022210698859/5000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6358734022210698859/2500000000000000000 : ℝ) ≤ (3140338788504739/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (6358734022210698859/2500000000000000000 : ℝ)^32 ≤ (3140338788504739/2500000000000000 : ℝ)^131 := by
      have hnat : (6358734022210698859 : ℕ)^32*2500000000000000^131 ≤ 3140338788504739^131*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6358734022210698859 2500000000000000000 3140338788504739 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3140338788504739/2500000000000000 : ℝ)) (X := (6358734022210698859/2500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(3998617950429/25031200000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(353957807536027/3128900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (93867/100000 : ℝ)) (alpha := (3998617950429/25031200000000 : ℝ)) (beta := (353957807536027/3128900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (93867/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(3998617950429/25031200000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(353957807536027/3128900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5197/6250 : ℝ) ^ (131/32 : ℝ) ≤ (46987124006863807447/100000000000000000000 : ℝ) := by
    have hpowers : (5197/6250 : ℝ)^131 ≤ (46987124006863807447/100000000000000000000 : ℝ)^32 := by
      have hnat : (5197 : ℕ)^131*100000000000000000000^32 ≤ 46987124006863807447^32*6250^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5197 6250 46987124006863807447 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5197/6250 : ℝ)) (X := (46987124006863807447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (146987124006863807447/100000000000000000000 : ℝ) ≤ (10986569749815241/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (146987124006863807447/100000000000000000000 : ℝ)^32 ≤ (10986569749815241/10000000000000000 : ℝ)^131 := by
      have hnat : (146987124006863807447 : ℕ)^32*10000000000000000^131 ≤ 10986569749815241^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        146987124006863807447 100000000000000000000 10986569749815241 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10986569749815241/10000000000000000 : ℝ)) (X := (146987124006863807447/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (96987124006863807447/50000000000000000000 : ℝ) ≤ (11756786442348153/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (96987124006863807447/50000000000000000000 : ℝ)^32 ≤ (11756786442348153/10000000000000000 : ℝ)^131 := by
      have hnat : (96987124006863807447 : ℕ)^32*10000000000000000^131 ≤ 11756786442348153^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96987124006863807447 50000000000000000000 11756786442348153 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11756786442348153/10000000000000000 : ℝ)) (X := (96987124006863807447/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(986569749815241/8315200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(48138543283307/519700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (5197/6250 : ℝ)) (alpha := (986569749815241/8315200000000000 : ℝ)) (beta := (48138543283307/519700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5197/6250 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(986569749815241/8315200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(48138543283307/519700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-466080199/5000000000 : ℝ)*X 0 0+(63441871/125000000 : ℝ)*X 0 1+(-6338972877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((509670227/1000000000 : ℝ)*X 1 0+(-460663689/5000000000 : ℝ)*X 1 1+(-3162461639/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-315386893/2500000000 : ℝ)*X 0 0+(1985154159/10000000000 : ℝ)*X 0 1+(-2144334347/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((291577929/1250000000 : ℝ)*X 1 0+(-431012067/5000000000 : ℝ)*X 1 1+(-4279199463/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2629979217/10000000000 : ℝ)*X 2 0+(76233219/100000000 : ℝ)*X 2 1+(2126155739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((730160253/2000000000 : ℝ)*X 0 0+(61906501/78125000 : ℝ)*X 0 1+(-1/2000000000 : ℝ)*X 0 2+(730160253/2000000000 : ℝ)*X 1 0+(61906501/78125000 : ℝ)*X 1 1+(-1/2000000000 : ℝ)*X 1 2+(730160253/2000000000 : ℝ)*X 2 0+(61906501/78125000 : ℝ)*X 2 1+(-1/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-49485119/500000000 : ℝ)*X 0 0+(2150842971/10000000000 : ℝ)*X 0 1+(-4307040651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1848168549/10000000000 : ℝ)*X 1 0+(-691776571/5000000000 : ℝ)*X 1 1+(-8595062141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3681449171/5000000000 : ℝ)*X 2 0+(585781441/2000000000 : ℝ)*X 2 1+(2189903373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8150839259/10000000000 : ℝ)*X 0 0+(134197173/400000000 : ℝ)*X 0 1+(287/10000000000 : ℝ)*X 0 2+(8150839259/10000000000 : ℝ)*X 1 0+(134197173/400000000 : ℝ)*X 1 1+(287/10000000000 : ℝ)*X 1 2+(8150839259/10000000000 : ℝ)*X 2 0+(134197173/400000000 : ℝ)*X 2 1+(287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-406647043/10000000000 : ℝ)*X 0 0+(889134377/1250000000 : ℝ)*X 0 1+(-224525483/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((94173953/125000000 : ℝ)*X 1 0+(-18985757/400000000 : ℝ)*X 1 1+(-791109947/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2297462781/10000000000 : ℝ)*X 2 0+(477708723/625000000 : ℝ)*X 2 1+(2437470979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8408226657/10000000000 : ℝ)*X 0 0+(597739073/2000000000 : ℝ)*X 0 1+(-18050003/2500000000 : ℝ)*X 0 2+(8408226657/10000000000 : ℝ)*X 1 0+(597739073/2000000000 : ℝ)*X 1 1+(-18050003/2500000000 : ℝ)*X 1 2+(8408226657/10000000000 : ℝ)*X 2 0+(597739073/2000000000 : ℝ)*X 2 1+(-18050003/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((86563/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86563/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4815078202969311562993210773/263475011440000000000000000000000 : ℝ) := by norm_num
    linear_combination (72704778627/1000000000000 : ℝ)*(base5) + (456614017959/500000000000 : ℝ)*(base7) + (36943062707/20000000000 : ℝ)*(major_s1_0) + (36943062707/20000000000 : ℝ)*(major_s1_1) + (36943062707/20000000000 : ℝ)*(major_s1_2) + (3899671/1000000000000 : ℝ)*(sp_s1_0) + (4667291/1000000000000 : ℝ)*(sp_s1_1) + (119367037999/62500000000 : ℝ)*(sp_s1_7) + (190979145509/100000000000 : ℝ)*(sp_s1_8) + (1982557455869/1000000000000 : ℝ)*(sp_s1_9) + (129282518073/62500000000 : ℝ)*(sp_s1_13) + (33323139/1000000000000 : ℝ)*(sp_s1_14) + (113708413/1000000000000 : ℝ)*(sp_s1_15) + (57153553/1000000000000 : ℝ)*(sp_s1_23) + (1227997031877/1000000000000 : ℝ)*(f.failure) + (954954915397/500000000000 : ℝ)*(f.sum) + (2876261402419138383/26017429280000000000000000000000 : ℝ)*base63 + (3018653680259/6496250000000000000000000 : ℝ)*base65 + (161769021374996349/156445000000000000000000000 : ℝ)*base67 + (111362442710471/831520000000000000000000000 : ℝ)*base69 + (19702122301885633/70523290000000000000000000000 : ℝ)*base71 + (28060566120847641/27140000000000000000000000 : ℝ)*base73 + (12601014215421/312890000000000000000000000 : ℝ)*base75 + (358298832097/3392500000000000000000000 : ℝ)*base77 + (35129288469739087281/33967338400000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (3083/5000000000000000 : ℝ)*base86 + (3083/5000000000000000 : ℝ)*base88 + (3083/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43049/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43049/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1169695545031741970425468784337/110330161040500000000000000000000000 : ℝ) := by norm_num
    linear_combination (11431250221/500000000000 : ℝ)*(base5) + (915273803237/1000000000000 : ℝ)*(base7) + (22210135477/1000000000000 : ℝ)*(base60) + (228071070601/125000000000 : ℝ)*(major_s1_0) + (228071070601/125000000000 : ℝ)*(major_s1_1) + (228071070601/125000000000 : ℝ)*(major_s1_2) + (4235399/1000000000000 : ℝ)*(sp_s1_0) + (1796149/500000000000 : ℝ)*(sp_s1_1) + (6485857/200000000000 : ℝ)*(sp_s1_7) + (6104599/100000000000 : ℝ)*(sp_s1_8) + (1878474521971/1000000000000 : ℝ)*(sp_s1_14) + (1878446548367/1000000000000 : ℝ)*(sp_s1_15) + (1901373687097/1000000000000 : ℝ)*(sp_s1_16) + (2105393994463/1000000000000 : ℝ)*(sp_s1_20) + (303245672917/250000000000 : ℝ)*(f.failure) + (375702237331/200000000000 : ℝ)*(f.sum) + (6538807158379355149/32521786600000000000000000000000 : ℝ)*base63 + (122838064483293/259850000000000000000000000 : ℝ)*base65 + (74203810421903/391112500000000000000000000 : ℝ)*base66 + (498891445862241/1039400000000000000000000000 : ℝ)*base69 + (658590029305514651/1763082250000000000000000000000 : ℝ)*base71 + (6642211888717/84812500000000000000000000 : ℝ)*base72 + (182422538411601/312890000000000000000000000 : ℝ)*base75 + (8784574547523/21203125000000000000000000 : ℝ)*base77 + (2270398890809713/41464036132812500000000000000 : ℝ)*base79 + (1243/1250000000000000 : ℝ)*base86 + (1243/1250000000000000 : ℝ)*base88 + (1243/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-71347/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-71347/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1957170124770763265095209118347/176528257664800000000000000000000000 : ℝ) := by norm_num
    linear_combination (700009486367/1000000000000 : ℝ)*(base7) + (28095336457/1000000000000 : ℝ)*(base39) + (11233347471/100000000000 : ℝ)*(base43) + (1118477/500000000000 : ℝ)*(base50) + (29890730419/1000000000000 : ℝ)*(base59) + (328387156351/200000000000 : ℝ)*(major_s1_0) + (305920461409/200000000000 : ℝ)*(major_s1_1) + (328387156351/200000000000 : ℝ)*(major_s1_2) + (20611367/100000000000 : ℝ)*(sp_s1_9) + (45022183/1000000000000 : ℝ)*(sp_s1_20) + (826739573929/500000000000 : ℝ)*(sp_s1_21) + (1765812622567/1000000000000 : ℝ)*(sp_s1_22) + (413318258547/250000000000 : ℝ)*(sp_s1_23) + (223941491223/125000000000 : ℝ)*(sp_s1_27) + (1091567465599/1000000000000 : ℝ)*(f.failure) + (1765812622567/1000000000000 : ℝ)*(f.sum) + (16168773460827689903/52034858560000000000000000000000 : ℝ)*base63 + (6375931891547/20788000000000000000000000 : ℝ)*base65 + (324927927245431/625780000000000000000000000 : ℝ)*base66 + (911043886695831/1663040000000000000000000000 : ℝ)*base69 + (338014870311712469/705232900000000000000000000000 : ℝ)*base71 + (23016794667329/271400000000000000000000000 : ℝ)*base72 + (312161153329291/625780000000000000000000000 : ℝ)*base75 + (11224630358619/67850000000000000000000000 : ℝ)*base76 + (218999573450260991/8491834600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (4921/5000000000000000 : ℝ)*base86 + (4921/5000000000000000 : ℝ)*base88 + (4921/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((9499/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9499/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93867/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(93867/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5197/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5197/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((86563/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86563/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43049/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43049/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-71347/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-71347/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303062_s1 p hpa hpb X hX hprev0

#print axioms solution
