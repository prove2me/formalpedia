-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310075_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:16.601089+00:00
-- url     : https://prove2.me/submissions/73e6a1b2-076a-481a-9086-c23a44055426

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
theorem collision_support_c310075_s1_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (264887813/500000000 : ℝ)*x 0 + (-155596773/400000000 : ℝ)*x 1 + (-3564663849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264887813/500000000 : ℝ)^71 ≤ (22019011813071/50000000000000 : ℝ)^55 := by
    have hnat : (264887813 : ℕ)^71*50000000000000^55 ≤ 22019011813071^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264887813 500000000 22019011813071 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155596773/400000000 : ℝ)^71 ≤ (29556335348583/100000000000000 : ℝ)^55 := by
    have hnat : (155596773 : ℕ)^71*100000000000000^55 ≤ 29556335348583^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155596773 400000000 29556335348583 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3564663849/10000000000 : ℝ)^71 ≤ (1650352563007/6250000000000 : ℝ)^55 := by
    have hnat : (3564663849 : ℕ)^71*6250000000000^55 ≤ 1650352563007^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3564663849 10000000000 1650352563007 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264887813/500000000 : ℝ), (-155596773/400000000 : ℝ), (-3564663849/10000000000 : ℝ)] ![(22019011813071/50000000000000 : ℝ), (29556335348583/100000000000000 : ℝ), (1650352563007/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264887813/500000000 : ℝ)|^71 ≤ (22019011813071/50000000000000 : ℝ)^55
        have hw : |(264887813/500000000 : ℝ)|=(264887813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155596773/400000000 : ℝ)|^71 ≤ (29556335348583/100000000000000 : ℝ)^55
        have hw : |(-155596773/400000000 : ℝ)|=(155596773/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3564663849/10000000000 : ℝ)|^71 ≤ (1650352563007/6250000000000 : ℝ)^55
        have hw : |(-3564663849/10000000000 : ℝ)|=(3564663849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2660822053/10000000000 : ℝ)*x 0 + (-1103440303/5000000000 : ℝ)*x 1 + (3695095281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2660822053/10000000000 : ℝ)^71 ≤ (18102881540877/100000000000000 : ℝ)^55 := by
    have hnat : (2660822053 : ℕ)^71*100000000000000^55 ≤ 18102881540877^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2660822053 10000000000 18102881540877 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103440303/5000000000 : ℝ)^71 ≤ (7109648680303/50000000000000 : ℝ)^55 := by
    have hnat : (1103440303 : ℕ)^71*50000000000000^55 ≤ 7109648680303^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103440303 5000000000 7109648680303 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3695095281/5000000000 : ℝ)^71 ≤ (67677821087547/100000000000000 : ℝ)^55 := by
    have hnat : (3695095281 : ℕ)^71*100000000000000^55 ≤ 67677821087547^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695095281 5000000000 67677821087547 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2660822053/10000000000 : ℝ), (-1103440303/5000000000 : ℝ), (3695095281/5000000000 : ℝ)] ![(18102881540877/100000000000000 : ℝ), (7109648680303/50000000000000 : ℝ), (67677821087547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2660822053/10000000000 : ℝ)|^71 ≤ (18102881540877/100000000000000 : ℝ)^55
        have hw : |(2660822053/10000000000 : ℝ)|=(2660822053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103440303/5000000000 : ℝ)|^71 ≤ (7109648680303/50000000000000 : ℝ)^55
        have hw : |(-1103440303/5000000000 : ℝ)|=(1103440303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3695095281/5000000000 : ℝ)|^71 ≤ (67677821087547/100000000000000 : ℝ)^55
        have hw : |(3695095281/5000000000 : ℝ)|=(3695095281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-283108387/10000000000 : ℝ)*x 0 + (-1510166083/2000000000 : ℝ)*x 1 + (3875341193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283108387/10000000000 : ℝ)^71 ≤ (125464750117/12500000000000 : ℝ)^55 := by
    have hnat : (283108387 : ℕ)^71*12500000000000^55 ≤ 125464750117^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283108387 10000000000 125464750117 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510166083/2000000000 : ℝ)^71 ≤ (34791429616711/50000000000000 : ℝ)^55 := by
    have hnat : (1510166083 : ℕ)^71*50000000000000^55 ≤ 34791429616711^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510166083 2000000000 34791429616711 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3875341193/10000000000 : ℝ)^71 ≤ (29413422750941/100000000000000 : ℝ)^55 := by
    have hnat : (3875341193 : ℕ)^71*100000000000000^55 ≤ 29413422750941^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875341193 10000000000 29413422750941 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283108387/10000000000 : ℝ), (-1510166083/2000000000 : ℝ), (3875341193/10000000000 : ℝ)] ![(125464750117/12500000000000 : ℝ), (34791429616711/50000000000000 : ℝ), (29413422750941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283108387/10000000000 : ℝ)|^71 ≤ (125464750117/12500000000000 : ℝ)^55
        have hw : |(-283108387/10000000000 : ℝ)|=(283108387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1510166083/2000000000 : ℝ)|^71 ≤ (34791429616711/50000000000000 : ℝ)^55
        have hw : |(-1510166083/2000000000 : ℝ)|=(1510166083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3875341193/10000000000 : ℝ)|^71 ≤ (29413422750941/100000000000000 : ℝ)^55
        have hw : |(3875341193/10000000000 : ℝ)|=(3875341193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6801871889/10000000000 : ℝ)*x 0 + (285648739/1000000000 : ℝ)*x 1 + (2802384611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6801871889/10000000000 : ℝ)^71 ≤ (1520122371337/2500000000000 : ℝ)^55 := by
    have hnat : (6801871889 : ℕ)^71*2500000000000^55 ≤ 1520122371337^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6801871889 10000000000 1520122371337 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285648739/1000000000 : ℝ)^71 ≤ (4959855137369/25000000000000 : ℝ)^55 := by
    have hnat : (285648739 : ℕ)^71*25000000000000^55 ≤ 4959855137369^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285648739 1000000000 4959855137369 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2802384611/10000000000 : ℝ)^71 ≤ (3871136917099/20000000000000 : ℝ)^55 := by
    have hnat : (2802384611 : ℕ)^71*20000000000000^55 ≤ 3871136917099^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802384611 10000000000 3871136917099 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6801871889/10000000000 : ℝ), (285648739/1000000000 : ℝ), (2802384611/10000000000 : ℝ)] ![(1520122371337/2500000000000 : ℝ), (4959855137369/25000000000000 : ℝ), (3871136917099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6801871889/10000000000 : ℝ)|^71 ≤ (1520122371337/2500000000000 : ℝ)^55
        have hw : |(6801871889/10000000000 : ℝ)|=(6801871889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285648739/1000000000 : ℝ)|^71 ≤ (4959855137369/25000000000000 : ℝ)^55
        have hw : |(285648739/1000000000 : ℝ)|=(285648739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2802384611/10000000000 : ℝ)|^71 ≤ (3871136917099/20000000000000 : ℝ)^55
        have hw : |(2802384611/10000000000 : ℝ)|=(2802384611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5395446349/10000000000 : ℝ)*x 0 + (-1895740309/5000000000 : ℝ)*x 1 + (-711068047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395446349/10000000000 : ℝ)^71 ≤ (45089114531399/100000000000000 : ℝ)^55 := by
    have hnat : (5395446349 : ℕ)^71*100000000000000^55 ≤ 45089114531399^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395446349 10000000000 45089114531399 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895740309/5000000000 : ℝ)^71 ≤ (7148592011991/25000000000000 : ℝ)^55 := by
    have hnat : (1895740309 : ℕ)^71*25000000000000^55 ≤ 7148592011991^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895740309 5000000000 7148592011991 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711068047/2000000000 : ℝ)^71 ≤ (13158258704333/50000000000000 : ℝ)^55 := by
    have hnat : (711068047 : ℕ)^71*50000000000000^55 ≤ 13158258704333^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711068047 2000000000 13158258704333 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395446349/10000000000 : ℝ), (-1895740309/5000000000 : ℝ), (-711068047/2000000000 : ℝ)] ![(45089114531399/100000000000000 : ℝ), (7148592011991/25000000000000 : ℝ), (13158258704333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395446349/10000000000 : ℝ)|^71 ≤ (45089114531399/100000000000000 : ℝ)^55
        have hw : |(5395446349/10000000000 : ℝ)|=(5395446349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895740309/5000000000 : ℝ)|^71 ≤ (7148592011991/25000000000000 : ℝ)^55
        have hw : |(-1895740309/5000000000 : ℝ)|=(1895740309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-711068047/2000000000 : ℝ)|^71 ≤ (13158258704333/50000000000000 : ℝ)^55
        have hw : |(-711068047/2000000000 : ℝ)|=(711068047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (102468421/1250000000 : ℝ)*x 0 + (-306037311/5000000000 : ℝ)*x 1 + (4739448627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102468421/1250000000 : ℝ)^71 ≤ (1979838114017/50000000000000 : ℝ)^55 := by
    have hnat : (102468421 : ℕ)^71*50000000000000^55 ≤ 1979838114017^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102468421 1250000000 1979838114017 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306037311/5000000000 : ℝ)^71 ≤ (2715655877137/100000000000000 : ℝ)^55 := by
    have hnat : (306037311 : ℕ)^71*100000000000000^55 ≤ 2715655877137^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306037311 5000000000 2715655877137 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4739448627/5000000000 : ℝ)^71 ≤ (93324667890231/100000000000000 : ℝ)^55 := by
    have hnat : (4739448627 : ℕ)^71*100000000000000^55 ≤ 93324667890231^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4739448627 5000000000 93324667890231 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(102468421/1250000000 : ℝ), (-306037311/5000000000 : ℝ), (4739448627/5000000000 : ℝ)] ![(1979838114017/50000000000000 : ℝ), (2715655877137/100000000000000 : ℝ), (93324667890231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(102468421/1250000000 : ℝ)|^71 ≤ (1979838114017/50000000000000 : ℝ)^55
        have hw : |(102468421/1250000000 : ℝ)|=(102468421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306037311/5000000000 : ℝ)|^71 ≤ (2715655877137/100000000000000 : ℝ)^55
        have hw : |(-306037311/5000000000 : ℝ)|=(306037311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4739448627/5000000000 : ℝ)|^71 ≤ (93324667890231/100000000000000 : ℝ)^55
        have hw : |(4739448627/5000000000 : ℝ)|=(4739448627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-110796247/10000000000 : ℝ)*x 0 + (-6171393557/10000000000 : ℝ)*x 1 + (5486287643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110796247/10000000000 : ℝ)^71 ≤ (298992028557/100000000000000 : ℝ)^55 := by
    have hnat : (110796247 : ℕ)^71*100000000000000^55 ≤ 298992028557^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110796247 10000000000 298992028557 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6171393557/10000000000 : ℝ)^71 ≤ (429036073621/800000000000 : ℝ)^55 := by
    have hnat : (6171393557 : ℕ)^71*800000000000^55 ≤ 429036073621^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6171393557 10000000000 429036073621 800000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486287643/10000000000 : ℝ)^71 ≤ (368571990063/800000000000 : ℝ)^55 := by
    have hnat : (5486287643 : ℕ)^71*800000000000^55 ≤ 368571990063^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486287643 10000000000 368571990063 800000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110796247/10000000000 : ℝ), (-6171393557/10000000000 : ℝ), (5486287643/10000000000 : ℝ)] ![(298992028557/100000000000000 : ℝ), (429036073621/800000000000 : ℝ), (368571990063/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110796247/10000000000 : ℝ)|^71 ≤ (298992028557/100000000000000 : ℝ)^55
        have hw : |(-110796247/10000000000 : ℝ)|=(110796247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6171393557/10000000000 : ℝ)|^71 ≤ (429036073621/800000000000 : ℝ)^55
        have hw : |(-6171393557/10000000000 : ℝ)|=(6171393557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486287643/10000000000 : ℝ)|^71 ≤ (368571990063/800000000000 : ℝ)^55
        have hw : |(5486287643/10000000000 : ℝ)|=(5486287643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7786928559/10000000000 : ℝ)*x 0 + (4418757/19531250 : ℝ)*x 1 + (128008809/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7786928559/10000000000 : ℝ)^71 ≤ (72404178013297/100000000000000 : ℝ)^55 := by
    have hnat : (7786928559 : ℕ)^71*100000000000000^55 ≤ 72404178013297^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7786928559 10000000000 72404178013297 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4418757/19531250 : ℝ)^71 ≤ (1835349009943/12500000000000 : ℝ)^55 := by
    have hnat : (4418757 : ℕ)^71*12500000000000^55 ≤ 1835349009943^55*19531250^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418757 19531250 1835349009943 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128008809/625000000 : ℝ)^71 ≤ (258260597933/2000000000000 : ℝ)^55 := by
    have hnat : (128008809 : ℕ)^71*2000000000000^55 ≤ 258260597933^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128008809 625000000 258260597933 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7786928559/10000000000 : ℝ), (4418757/19531250 : ℝ), (128008809/625000000 : ℝ)] ![(72404178013297/100000000000000 : ℝ), (1835349009943/12500000000000 : ℝ), (258260597933/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7786928559/10000000000 : ℝ)|^71 ≤ (72404178013297/100000000000000 : ℝ)^55
        have hw : |(7786928559/10000000000 : ℝ)|=(7786928559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4418757/19531250 : ℝ)|^71 ≤ (1835349009943/12500000000000 : ℝ)^55
        have hw : |(4418757/19531250 : ℝ)|=(4418757/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128008809/625000000 : ℝ)|^71 ≤ (258260597933/2000000000000 : ℝ)^55
        have hw : |(128008809/625000000 : ℝ)|=(128008809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (762510463/1250000000 : ℝ)*x 0 + (-3697638663/10000000000 : ℝ)*x 1 + (-2816881603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (762510463/1250000000 : ℝ)^71 ≤ (13207725494483/25000000000000 : ℝ)^55 := by
    have hnat : (762510463 : ℕ)^71*25000000000000^55 ≤ 13207725494483^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762510463 1250000000 13207725494483 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3697638663/10000000000 : ℝ)^71 ≤ (13842029601873/50000000000000 : ℝ)^55 := by
    have hnat : (3697638663 : ℕ)^71*50000000000000^55 ≤ 13842029601873^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3697638663 10000000000 13842029601873 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2816881603/10000000000 : ℝ)^71 ≤ (9742519405329/50000000000000 : ℝ)^55 := by
    have hnat : (2816881603 : ℕ)^71*50000000000000^55 ≤ 9742519405329^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816881603 10000000000 9742519405329 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(762510463/1250000000 : ℝ), (-3697638663/10000000000 : ℝ), (-2816881603/10000000000 : ℝ)] ![(13207725494483/25000000000000 : ℝ), (13842029601873/50000000000000 : ℝ), (9742519405329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(762510463/1250000000 : ℝ)|^71 ≤ (13207725494483/25000000000000 : ℝ)^55
        have hw : |(762510463/1250000000 : ℝ)|=(762510463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3697638663/10000000000 : ℝ)|^71 ≤ (13842029601873/50000000000000 : ℝ)^55
        have hw : |(-3697638663/10000000000 : ℝ)|=(3697638663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2816881603/10000000000 : ℝ)|^71 ≤ (9742519405329/50000000000000 : ℝ)^55
        have hw : |(-2816881603/10000000000 : ℝ)|=(2816881603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (530729993/5000000000 : ℝ)*x 0 + (-226059967/2500000000 : ℝ)*x 1 + (8998554/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530729993/5000000000 : ℝ)^71 ≤ (1105503527111/20000000000000 : ℝ)^55 := by
    have hnat : (530729993 : ℕ)^71*20000000000000^55 ≤ 1105503527111^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530729993 5000000000 1105503527111 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226059967/2500000000 : ℝ)^71 ≤ (2247124223363/50000000000000 : ℝ)^55 := by
    have hnat : (226059967 : ℕ)^71*50000000000000^55 ≤ 2247124223363^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226059967 2500000000 2247124223363 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8998554/9765625 : ℝ)^71 ≤ (89978233906141/100000000000000 : ℝ)^55 := by
    have hnat : (8998554 : ℕ)^71*100000000000000^55 ≤ 89978233906141^55*9765625^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8998554 9765625 89978233906141 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530729993/5000000000 : ℝ), (-226059967/2500000000 : ℝ), (8998554/9765625 : ℝ)] ![(1105503527111/20000000000000 : ℝ), (2247124223363/50000000000000 : ℝ), (89978233906141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530729993/5000000000 : ℝ)|^71 ≤ (1105503527111/20000000000000 : ℝ)^55
        have hw : |(530729993/5000000000 : ℝ)|=(530729993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226059967/2500000000 : ℝ)|^71 ≤ (2247124223363/50000000000000 : ℝ)^55
        have hw : |(-226059967/2500000000 : ℝ)|=(226059967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8998554/9765625 : ℝ)|^71 ≤ (89978233906141/100000000000000 : ℝ)^55
        have hw : |(8998554/9765625 : ℝ)|=(8998554/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-65319747/5000000000 : ℝ)*x 0 + (-1871038627/2500000000 : ℝ)*x 1 + (4020106443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65319747/5000000000 : ℝ)^71 ≤ (92462033529/25000000000000 : ℝ)^55 := by
    have hnat : (65319747 : ℕ)^71*25000000000000^55 ≤ 92462033529^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65319747 5000000000 92462033529 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1871038627/2500000000 : ℝ)^71 ≤ (17197674854773/25000000000000 : ℝ)^55 := by
    have hnat : (1871038627 : ℕ)^71*25000000000000^55 ≤ 17197674854773^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871038627 2500000000 17197674854773 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020106443/10000000000 : ℝ)^71 ≤ (30839452440031/100000000000000 : ℝ)^55 := by
    have hnat : (4020106443 : ℕ)^71*100000000000000^55 ≤ 30839452440031^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020106443 10000000000 30839452440031 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65319747/5000000000 : ℝ), (-1871038627/2500000000 : ℝ), (4020106443/10000000000 : ℝ)] ![(92462033529/25000000000000 : ℝ), (17197674854773/25000000000000 : ℝ), (30839452440031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65319747/5000000000 : ℝ)|^71 ≤ (92462033529/25000000000000 : ℝ)^55
        have hw : |(-65319747/5000000000 : ℝ)|=(65319747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1871038627/2500000000 : ℝ)|^71 ≤ (17197674854773/25000000000000 : ℝ)^55
        have hw : |(-1871038627/2500000000 : ℝ)|=(1871038627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020106443/10000000000 : ℝ)|^71 ≤ (30839452440031/100000000000000 : ℝ)^55
        have hw : |(4020106443/10000000000 : ℝ)|=(4020106443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (500159721/625000000 : ℝ)*x 0 + (2095333439/10000000000 : ℝ)*x 1 + (379463207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500159721/625000000 : ℝ)^71 ≤ (37501362707789/50000000000000 : ℝ)^55 := by
    have hnat : (500159721 : ℕ)^71*50000000000000^55 ≤ 37501362707789^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500159721 625000000 37501362707789 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095333439/10000000000 : ℝ)^71 ≤ (6649201854321/50000000000000 : ℝ)^55 := by
    have hnat : (2095333439 : ℕ)^71*50000000000000^55 ≤ 6649201854321^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095333439 10000000000 6649201854321 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379463207/2000000000 : ℝ)^71 ≤ (2924717714183/25000000000000 : ℝ)^55 := by
    have hnat : (379463207 : ℕ)^71*25000000000000^55 ≤ 2924717714183^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379463207 2000000000 2924717714183 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(500159721/625000000 : ℝ), (2095333439/10000000000 : ℝ), (379463207/2000000000 : ℝ)] ![(37501362707789/50000000000000 : ℝ), (6649201854321/50000000000000 : ℝ), (2924717714183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(500159721/625000000 : ℝ)|^71 ≤ (37501362707789/50000000000000 : ℝ)^55
        have hw : |(500159721/625000000 : ℝ)|=(500159721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2095333439/10000000000 : ℝ)|^71 ≤ (6649201854321/50000000000000 : ℝ)^55
        have hw : |(2095333439/10000000000 : ℝ)|=(2095333439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(379463207/2000000000 : ℝ)|^71 ≤ (2924717714183/25000000000000 : ℝ)^55
        have hw : |(379463207/2000000000 : ℝ)|=(379463207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4597987047/10000000000 : ℝ)*x 0 + (-2276317393/5000000000 : ℝ)*x 1 + (-3638139023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4597987047/10000000000 : ℝ)^71 ≤ (36677998844903/100000000000000 : ℝ)^55 := by
    have hnat : (4597987047 : ℕ)^71*100000000000000^55 ≤ 36677998844903^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597987047 10000000000 36677998844903 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276317393/5000000000 : ℝ)^71 ≤ (36211653651643/100000000000000 : ℝ)^55 := by
    have hnat : (2276317393 : ℕ)^71*100000000000000^55 ≤ 36211653651643^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276317393 5000000000 36211653651643 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3638139023/10000000000 : ℝ)^71 ≤ (1694396718077/6250000000000 : ℝ)^55 := by
    have hnat : (3638139023 : ℕ)^71*6250000000000^55 ≤ 1694396718077^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3638139023 10000000000 1694396718077 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4597987047/10000000000 : ℝ), (-2276317393/5000000000 : ℝ), (-3638139023/10000000000 : ℝ)] ![(36677998844903/100000000000000 : ℝ), (36211653651643/100000000000000 : ℝ), (1694396718077/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4597987047/10000000000 : ℝ)|^71 ≤ (36677998844903/100000000000000 : ℝ)^55
        have hw : |(4597987047/10000000000 : ℝ)|=(4597987047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276317393/5000000000 : ℝ)|^71 ≤ (36211653651643/100000000000000 : ℝ)^55
        have hw : |(-2276317393/5000000000 : ℝ)|=(2276317393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3638139023/10000000000 : ℝ)|^71 ≤ (1694396718077/6250000000000 : ℝ)^55
        have hw : |(-3638139023/10000000000 : ℝ)|=(3638139023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310075_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3893457947/10000000000 : ℝ)*x 0 + (-76115257/1000000000 : ℝ)*x 1 + (146334843/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3893457947/10000000000 : ℝ)^71 ≤ (29591048758171/100000000000000 : ℝ)^55 := by
    have hnat : (3893457947 : ℕ)^71*100000000000000^55 ≤ 29591048758171^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893457947 10000000000 29591048758171 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76115257/1000000000 : ℝ)^71 ≤ (3598169951737/100000000000000 : ℝ)^55 := by
    have hnat : (76115257 : ℕ)^71*100000000000000^55 ≤ 3598169951737^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76115257 1000000000 3598169951737 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146334843/200000000 : ℝ)^71 ≤ (66810781277841/100000000000000 : ℝ)^55 := by
    have hnat : (146334843 : ℕ)^71*100000000000000^55 ≤ 66810781277841^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146334843 200000000 66810781277841 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3893457947/10000000000 : ℝ), (-76115257/1000000000 : ℝ), (146334843/200000000 : ℝ)] ![(29591048758171/100000000000000 : ℝ), (3598169951737/100000000000000 : ℝ), (66810781277841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3893457947/10000000000 : ℝ)|^71 ≤ (29591048758171/100000000000000 : ℝ)^55
        have hw : |(3893457947/10000000000 : ℝ)|=(3893457947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76115257/1000000000 : ℝ)|^71 ≤ (3598169951737/100000000000000 : ℝ)^55
        have hw : |(-76115257/1000000000 : ℝ)|=(76115257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146334843/200000000 : ℝ)|^71 ≤ (66810781277841/100000000000000 : ℝ)^55
        have hw : |(146334843/200000000 : ℝ)|=(146334843/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310075_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((76421/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76421/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2731/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2731/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82353/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21643/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21643/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-64873/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-64873/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(933/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(933/2000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (76421/100000 : ℝ) ^ (35/8 : ℝ) ≤ (15417914685685957687/50000000000000000000 : ℝ) := by
    have hpowers : (76421/100000 : ℝ)^35 ≤ (15417914685685957687/50000000000000000000 : ℝ)^8 := by
      have hnat : (76421 : ℕ)^35*50000000000000000000^8 ≤ 15417914685685957687^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76421 100000 15417914685685957687 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76421/100000 : ℝ)) (X := (15417914685685957687/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (65417914685685957687/50000000000000000000 : ℝ) ≤ (2126720328524367/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (65417914685685957687/50000000000000000000 : ℝ)^8 ≤ (2126720328524367/2000000000000000 : ℝ)^35 := by
      have hnat : (65417914685685957687 : ℕ)^8*2000000000000000^35 ≤ 2126720328524367^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65417914685685957687 50000000000000000000 2126720328524367 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2126720328524367/2000000000000000 : ℝ)) (X := (65417914685685957687/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (40417914685685957687/25000000000000000000 : ℝ) ≤ (5580302622516473/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (40417914685685957687/25000000000000000000 : ℝ)^8 ≤ (5580302622516473/5000000000000000 : ℝ)^35 := by
      have hnat : (40417914685685957687 : ℕ)^8*5000000000000000^35 ≤ 5580302622516473^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40417914685685957687 25000000000000000000 5580302622516473 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5580302622516473/5000000000000000 : ℝ)) (X := (40417914685685957687/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(126720328524367/1528420000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(527003602411111/7642100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (76421/100000 : ℝ)) (alpha := (126720328524367/1528420000000000 : ℝ)) (beta := (527003602411111/7642100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (76421/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(126720328524367/1528420000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(527003602411111/7642100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2731/3125 : ℝ) ^ (35/8 : ℝ) ≤ (2772736488097483981/5000000000000000000 : ℝ) := by
    have hpowers : (2731/3125 : ℝ)^35 ≤ (2772736488097483981/5000000000000000000 : ℝ)^8 := by
      have hnat : (2731 : ℕ)^35*5000000000000000000^8 ≤ 2772736488097483981^8*3125^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2731 3125 2772736488097483981 5000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2731/3125 : ℝ)) (X := (2772736488097483981/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (7772736488097483981/5000000000000000000 : ℝ) ≤ (11061020222082937/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (7772736488097483981/5000000000000000000 : ℝ)^8 ≤ (11061020222082937/10000000000000000 : ℝ)^35 := by
      have hnat : (7772736488097483981 : ℕ)^8*10000000000000000^35 ≤ 11061020222082937^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7772736488097483981 5000000000000000000 11061020222082937 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11061020222082937/10000000000000000 : ℝ)) (X := (7772736488097483981/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5272736488097483981/2500000000000000000 : ℝ) ≤ (2371969469762689/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5272736488097483981/2500000000000000000 : ℝ)^8 ≤ (2371969469762689/2000000000000000 : ℝ)^35 := by
      have hnat : (5272736488097483981 : ℕ)^8*2000000000000000^35 ≤ 2371969469762689^35*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5272736488097483981 2500000000000000000 2371969469762689 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2371969469762689/2000000000000000 : ℝ)) (X := (5272736488097483981/2500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1061020222082937/8739200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(199706781682627/2184800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2731/3125 : ℝ)) (alpha := (1061020222082937/8739200000000000 : ℝ)) (beta := (199706781682627/2184800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (2731/3125 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1061020222082937/8739200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(199706781682627/2184800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (82353/100000 : ℝ) ^ (35/8 : ℝ) ≤ (42765886817379479003/100000000000000000000 : ℝ) := by
    have hpowers : (82353/100000 : ℝ)^35 ≤ (42765886817379479003/100000000000000000000 : ℝ)^8 := by
      have hnat : (82353 : ℕ)^35*100000000000000000000^8 ≤ 42765886817379479003^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82353 100000 42765886817379479003 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82353/100000 : ℝ)) (X := (42765886817379479003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (142765886817379479003/100000000000000000000 : ℝ) ≤ (2711956627193341/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (142765886817379479003/100000000000000000000 : ℝ)^8 ≤ (2711956627193341/2500000000000000 : ℝ)^35 := by
      have hnat : (142765886817379479003 : ℕ)^8*2500000000000000^35 ≤ 2711956627193341^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        142765886817379479003 100000000000000000000 2711956627193341 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2711956627193341/2500000000000000 : ℝ)) (X := (142765886817379479003/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (92765886817379479003/50000000000000000000 : ℝ) ≤ (11517355003311763/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (92765886817379479003/50000000000000000000 : ℝ)^8 ≤ (11517355003311763/10000000000000000 : ℝ)^35 := by
      have hnat : (92765886817379479003 : ℕ)^8*10000000000000000^35 ≤ 11517355003311763^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92765886817379479003 50000000000000000000 11517355003311763 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11517355003311763/10000000000000000 : ℝ)) (X := (92765886817379479003/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(70652209064447/686275000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(223176164846133/2745100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (82353/100000 : ℝ)) (alpha := (70652209064447/686275000000000 : ℝ)) (beta := (223176164846133/2745100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (82353/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(70652209064447/686275000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(223176164846133/2745100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_2 : ((264887813/500000000 : ℝ)*X 2 0+(-155596773/400000000 : ℝ)*X 2 1+(-3564663849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2660822053/10000000000 : ℝ)*X 0 0+(-1103440303/5000000000 : ℝ)*X 0 1+(3695095281/5000000000 : ℝ)*X 0 2+(2660822053/10000000000 : ℝ)*X 1 0+(-1103440303/5000000000 : ℝ)*X 1 1+(3695095281/5000000000 : ℝ)*X 1 2+(2660822053/10000000000 : ℝ)*X 2 0+(-1103440303/5000000000 : ℝ)*X 2 1+(3695095281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-283108387/10000000000 : ℝ)*X 0 0+(-1510166083/2000000000 : ℝ)*X 0 1+(3875341193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((6801871889/10000000000 : ℝ)*X 1 0+(285648739/1000000000 : ℝ)*X 1 1+(2802384611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5395446349/10000000000 : ℝ)*X 2 0+(-1895740309/5000000000 : ℝ)*X 2 1+(-711068047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((102468421/1250000000 : ℝ)*X 0 0+(-306037311/5000000000 : ℝ)*X 0 1+(4739448627/5000000000 : ℝ)*X 0 2+(102468421/1250000000 : ℝ)*X 1 0+(-306037311/5000000000 : ℝ)*X 1 1+(4739448627/5000000000 : ℝ)*X 1 2+(102468421/1250000000 : ℝ)*X 2 0+(-306037311/5000000000 : ℝ)*X 2 1+(4739448627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-110796247/10000000000 : ℝ)*X 0 0+(-6171393557/10000000000 : ℝ)*X 0 1+(5486287643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7786928559/10000000000 : ℝ)*X 1 0+(4418757/19531250 : ℝ)*X 1 1+(128008809/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((762510463/1250000000 : ℝ)*X 2 0+(-3697638663/10000000000 : ℝ)*X 2 1+(-2816881603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((530729993/5000000000 : ℝ)*X 0 0+(-226059967/2500000000 : ℝ)*X 0 1+(8998554/9765625 : ℝ)*X 0 2+(530729993/5000000000 : ℝ)*X 1 0+(-226059967/2500000000 : ℝ)*X 1 1+(8998554/9765625 : ℝ)*X 1 2+(530729993/5000000000 : ℝ)*X 2 0+(-226059967/2500000000 : ℝ)*X 2 1+(8998554/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-65319747/5000000000 : ℝ)*X 0 0+(-1871038627/2500000000 : ℝ)*X 0 1+(4020106443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((500159721/625000000 : ℝ)*X 1 0+(2095333439/10000000000 : ℝ)*X 1 1+(379463207/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4597987047/10000000000 : ℝ)*X 2 0+(-2276317393/5000000000 : ℝ)*X 2 1+(-3638139023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3893457947/10000000000 : ℝ)*X 0 0+(-76115257/1000000000 : ℝ)*X 0 1+(146334843/200000000 : ℝ)*X 0 2+(3893457947/10000000000 : ℝ)*X 1 0+(-76115257/1000000000 : ℝ)*X 1 1+(146334843/200000000 : ℝ)*X 1 2+(3893457947/10000000000 : ℝ)*X 2 0+(-76115257/1000000000 : ℝ)*X 2 1+(146334843/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310075_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((21643/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21643/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (123802162157636313931443017594073/9166690513121600000000000000000000000 : ℝ) := by norm_num
    linear_combination (67603/31250000000 : ℝ)*(base19) + (369302779601/1000000000000 : ℝ)*(base40) + (1117773/500000000000 : ℝ)*(base49) + (145701/200000000000 : ℝ)*(base54) + (208943/50000000000 : ℝ)*(base60) + (3853894341577/1000000000000 : ℝ)*(major_s1_0) + (3853894341577/1000000000000 : ℝ)*(major_s1_1) + (240868350817/62500000000 : ℝ)*(major_s1_2) + (8230043/10000000000 : ℝ)*(sp_s1_2) + (1331418882647/250000000000 : ℝ)*(sp_s1_7) + (2662895619327/500000000000 : ℝ)*(sp_s1_8) + (1064993933829/200000000000 : ℝ)*(sp_s1_9) + (238199005081/100000000000 : ℝ)*(sp_s1_13) + (58935681/500000000000 : ℝ)*(sp_s1_21) + (476398155863/200000000000 : ℝ)*(f.failure) + (106515868039/20000000000 : ℝ)*(f.sum) + (9396143321471252281/59974944800000000000000000000000 : ℝ)*base62 + (52930311964337/85784375000000000000000000 : ℝ)*base65 + (2304173440481151/8739200000000000000000000000 : ℝ)*base66 + (243496118239281/686275000000000000000000000 : ℝ)*base68 + (101675285117959257649/209783287100000000000000000000000 : ℝ)*base71 + (2967912757274093/7642100000000000000000000000 : ℝ)*base72 + (1424902926101579/2184800000000000000000000000 : ℝ)*base74 + (959466279873819/1528420000000000000000000000 : ℝ)*base77 + (161982677542742709147/667858403200000000000000000000000 : ℝ)*base78 + (2359/20000000000000000 : ℝ)*base87 + (2359/20000000000000000 : ℝ)*base89 + (2359/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-64873/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-64873/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (110545937425136562422300044901139/9166690513121600000000000000000000000 : ℝ) := by norm_num
    linear_combination (11106019/1000000000000 : ℝ)*(base13) + (31384851/1000000000000 : ℝ)*(base21) + (1049040321359/1000000000000 : ℝ)*(base40) + (46964358981/250000000000 : ℝ)*(base60) + (4847745500259/1000000000000 : ℝ)*(major_s1_0) + (4847745500259/1000000000000 : ℝ)*(major_s1_1) + (4847745500259/1000000000000 : ℝ)*(major_s1_2) + (110489761/1000000000000 : ℝ)*(sp_s1_9) + (42032803/500000000000 : ℝ)*(sp_s1_13) + (3349605910519/500000000000 : ℝ)*(sp_s1_14) + (1339814057519/200000000000 : ℝ)*(sp_s1_15) + (3349540526223/500000000000 : ℝ)*(sp_s1_16) + (1498089994003/500000000000 : ℝ)*(sp_s1_20) + (76319731/500000000000 : ℝ)*(sp_s1_22) + (2996264053611/1000000000000 : ℝ)*(f.failure) + (6699222927057/1000000000000 : ℝ)*(f.sum) + (29948218837802532467/59974944800000000000000000000000 : ℝ)*base62 + (100157953611613/2745100000000000000000000000 : ℝ)*base65 + (7195469114684597/8739200000000000000000000000 : ℝ)*base66 + (1003731668914509/1372550000000000000000000000 : ℝ)*base68 + (21835534047245721213/52445821775000000000000000000000 : ℝ)*base70 + (6997253007457751/7642100000000000000000000000 : ℝ)*base72 + (2273440654884953/2184800000000000000000000000 : ℝ)*base74 + (137013739525913/305684000000000000000000000 : ℝ)*base77 + (335435652937077440489/667858403200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (15477/100000000000000000 : ℝ)*base86 + (15477/100000000000000000 : ℝ)*base88 + (15477/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(933/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(933/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (116119663617924658719407877/8348230040000000000000000000000 : ℝ) := by norm_num
    linear_combination (1790889/250000000000 : ℝ)*(base22) + (988987377223/1000000000000 : ℝ)*(base40) + (66797948987/500000000000 : ℝ)*(base49) + (410531817839/100000000000 : ℝ)*(major_s1_0) + (410531817839/100000000000 : ℝ)*(major_s1_1) + (410531817839/100000000000 : ℝ)*(major_s1_2) + (30522663/1000000000000 : ℝ)*(sp_s1_6) + (765907171/1000000000000 : ℝ)*(sp_s1_7) + (22963533/500000000000 : ℝ)*(sp_s1_14) + (11322819/1000000000000 : ℝ)*(sp_s1_16) + (5672430642753/1000000000000 : ℝ)*(sp_s1_21) + (5673242476989/1000000000000 : ℝ)*(sp_s1_22) + (1134644798123/200000000000 : ℝ)*(sp_s1_23) + (2537358720623/1000000000000 : ℝ)*(sp_s1_27) + (1268694621643/500000000000 : ℝ)*(f.failure) + (5673242476989/1000000000000 : ℝ)*(f.sum) + (1239858742113998199/5997494480000000000000000000000 : ℝ)*base62 + (85092758662051/137255000000000000000000000 : ℝ)*base65 + (322565245616649/873920000000000000000000000 : ℝ)*base66 + (5163563373027/68627500000000000000000000 : ℝ)*base69 + (988996505436986761/4195665742000000000000000000000 : ℝ)*base70 + (95327105383319/382105000000000000000000000 : ℝ)*base73 + (140846301897701/218480000000000000000000000 : ℝ)*base74 + (15149881420967/38210500000000000000000000 : ℝ)*base77 + (31686696868410829043/66785840320000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (14101/50000000000000000 : ℝ)*base86 + (14101/50000000000000000 : ℝ)*base88 + (14101/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((76421/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76421/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2731/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2731/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82353/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21643/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21643/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-64873/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-64873/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(933/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(933/2000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310075_s1 p hpa hpb X hX hprev0

#print axioms solution
