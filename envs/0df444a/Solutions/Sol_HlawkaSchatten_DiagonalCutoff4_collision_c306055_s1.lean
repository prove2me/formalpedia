-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:08.155602+00:00
-- url     : https://prove2.me/submissions/df8b3e5c-65f6-4dc5-927c-f777014a7a2a

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
theorem collision_support_c306055_s1_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6646717161/10000000000 : ℝ)*x 0 + (3788998813/10000000000 : ℝ)*x 1 + (2161134179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6646717161/10000000000 : ℝ)^135 ≤ (7318210290727/12500000000000 : ℝ)^103 := by
    have hnat : (6646717161 : ℕ)^135*12500000000000^103 ≤ 7318210290727^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6646717161 10000000000 7318210290727 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3788998813/10000000000 : ℝ)^135 ≤ (350340727933/1250000000000 : ℝ)^103 := by
    have hnat : (3788998813 : ℕ)^135*1250000000000^103 ≤ 350340727933^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3788998813 10000000000 350340727933 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161134179/10000000000 : ℝ)^135 ≤ (268541188333/2000000000000 : ℝ)^103 := by
    have hnat : (2161134179 : ℕ)^135*2000000000000^103 ≤ 268541188333^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161134179 10000000000 268541188333 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6646717161/10000000000 : ℝ), (3788998813/10000000000 : ℝ), (2161134179/10000000000 : ℝ)] ![(7318210290727/12500000000000 : ℝ), (350340727933/1250000000000 : ℝ), (268541188333/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6646717161/10000000000 : ℝ)|^135 ≤ (7318210290727/12500000000000 : ℝ)^103
        have hw : |(6646717161/10000000000 : ℝ)|=(6646717161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3788998813/10000000000 : ℝ)|^135 ≤ (350340727933/1250000000000 : ℝ)^103
        have hw : |(3788998813/10000000000 : ℝ)|=(3788998813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2161134179/10000000000 : ℝ)|^135 ≤ (268541188333/2000000000000 : ℝ)^103
        have hw : |(2161134179/10000000000 : ℝ)|=(2161134179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055188427/5000000000 : ℝ)*x 0 + (4368918349/10000000000 : ℝ)*x 1 + (898520923/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055188427/5000000000 : ℝ)^135 ≤ (6236666703143/20000000000000 : ℝ)^103 := by
    have hnat : (2055188427 : ℕ)^135*20000000000000^103 ≤ 6236666703143^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055188427 5000000000 6236666703143 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4368918349/10000000000 : ℝ)^135 ≤ (33778895109067/100000000000000 : ℝ)^103 := by
    have hnat : (4368918349 : ℕ)^135*100000000000000^103 ≤ 33778895109067^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368918349 10000000000 33778895109067 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898520923/2000000000 : ℝ)^135 ≤ (17518885679519/50000000000000 : ℝ)^103 := by
    have hnat : (898520923 : ℕ)^135*50000000000000^103 ≤ 17518885679519^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898520923 2000000000 17518885679519 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055188427/5000000000 : ℝ), (4368918349/10000000000 : ℝ), (898520923/2000000000 : ℝ)] ![(6236666703143/20000000000000 : ℝ), (33778895109067/100000000000000 : ℝ), (17518885679519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055188427/5000000000 : ℝ)|^135 ≤ (6236666703143/20000000000000 : ℝ)^103
        have hw : |(-2055188427/5000000000 : ℝ)|=(2055188427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4368918349/10000000000 : ℝ)|^135 ≤ (33778895109067/100000000000000 : ℝ)^103
        have hw : |(4368918349/10000000000 : ℝ)|=(4368918349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898520923/2000000000 : ℝ)|^135 ≤ (17518885679519/50000000000000 : ℝ)^103
        have hw : |(898520923/2000000000 : ℝ)|=(898520923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (567728039/2500000000 : ℝ)*x 0 + (409631/2000000000 : ℝ)*x 1 + (8886955333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (567728039/2500000000 : ℝ)^135 ≤ (14327977972579/100000000000000 : ℝ)^103 := by
    have hnat : (567728039 : ℕ)^135*100000000000000^103 ≤ 14327977972579^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567728039 2500000000 14327977972579 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409631/2000000000 : ℝ)^135 ≤ (1463451903/100000000000000 : ℝ)^103 := by
    have hnat : (409631 : ℕ)^135*100000000000000^103 ≤ 1463451903^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409631 2000000000 1463451903 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8886955333/10000000000 : ℝ)^135 ≤ (8567055856457/10000000000000 : ℝ)^103 := by
    have hnat : (8886955333 : ℕ)^135*10000000000000^103 ≤ 8567055856457^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8886955333 10000000000 8567055856457 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(567728039/2500000000 : ℝ), (409631/2000000000 : ℝ), (8886955333/10000000000 : ℝ)] ![(14327977972579/100000000000000 : ℝ), (1463451903/100000000000000 : ℝ), (8567055856457/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(567728039/2500000000 : ℝ)|^135 ≤ (14327977972579/100000000000000 : ℝ)^103
        have hw : |(567728039/2500000000 : ℝ)|=(567728039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(409631/2000000000 : ℝ)|^135 ≤ (1463451903/100000000000000 : ℝ)^103
        have hw : |(409631/2000000000 : ℝ)|=(409631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8886955333/10000000000 : ℝ)|^135 ≤ (8567055856457/10000000000000 : ℝ)^103
        have hw : |(8886955333/10000000000 : ℝ)|=(8886955333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (946704129/5000000000 : ℝ)*x 0 + (8846735711/10000000000 : ℝ)*x 1 + (-782726729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946704129/5000000000 : ℝ)^135 ≤ (2822531550103/25000000000000 : ℝ)^103 := by
    have hnat : (946704129 : ℕ)^135*25000000000000^103 ≤ 2822531550103^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946704129 5000000000 2822531550103 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8846735711/10000000000 : ℝ)^135 ≤ (8516274138851/10000000000000 : ℝ)^103 := by
    have hnat : (8846735711 : ℕ)^135*10000000000000^103 ≤ 8516274138851^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8846735711 10000000000 8516274138851 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782726729/10000000000 : ℝ)^135 ≤ (1773566204077/50000000000000 : ℝ)^103 := by
    have hnat : (782726729 : ℕ)^135*50000000000000^103 ≤ 1773566204077^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782726729 10000000000 1773566204077 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(946704129/5000000000 : ℝ), (8846735711/10000000000 : ℝ), (-782726729/10000000000 : ℝ)] ![(2822531550103/25000000000000 : ℝ), (8516274138851/10000000000000 : ℝ), (1773566204077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(946704129/5000000000 : ℝ)|^135 ≤ (2822531550103/25000000000000 : ℝ)^103
        have hw : |(946704129/5000000000 : ℝ)|=(946704129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8846735711/10000000000 : ℝ)|^135 ≤ (8516274138851/10000000000000 : ℝ)^103
        have hw : |(8846735711/10000000000 : ℝ)|=(8846735711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-782726729/10000000000 : ℝ)|^135 ≤ (1773566204077/50000000000000 : ℝ)^103
        have hw : |(-782726729/10000000000 : ℝ)|=(782726729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3693400583/10000000000 : ℝ)*x 0 + (302571529/400000000 : ℝ)*x 1 + (780981597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3693400583/10000000000 : ℝ)^135 ≤ (6776019204319/25000000000000 : ℝ)^103 := by
    have hnat : (3693400583 : ℕ)^135*25000000000000^103 ≤ 6776019204319^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693400583 10000000000 6776019204319 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302571529/400000000 : ℝ)^135 ≤ (1083736761187/1562500000000 : ℝ)^103 := by
    have hnat : (302571529 : ℕ)^135*1562500000000^103 ≤ 1083736761187^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302571529 400000000 1083736761187 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780981597/10000000000 : ℝ)^135 ≤ (442096307111/12500000000000 : ℝ)^103 := by
    have hnat : (780981597 : ℕ)^135*12500000000000^103 ≤ 442096307111^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780981597 10000000000 442096307111 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3693400583/10000000000 : ℝ), (302571529/400000000 : ℝ), (780981597/10000000000 : ℝ)] ![(6776019204319/25000000000000 : ℝ), (1083736761187/1562500000000 : ℝ), (442096307111/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3693400583/10000000000 : ℝ)|^135 ≤ (6776019204319/25000000000000 : ℝ)^103
        have hw : |(3693400583/10000000000 : ℝ)|=(3693400583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(302571529/400000000 : ℝ)|^135 ≤ (1083736761187/1562500000000 : ℝ)^103
        have hw : |(302571529/400000000 : ℝ)|=(302571529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(780981597/10000000000 : ℝ)|^135 ≤ (442096307111/12500000000000 : ℝ)^103
        have hw : |(780981597/10000000000 : ℝ)|=(780981597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-489743203/2500000000 : ℝ)*x 0 + (2692770703/5000000000 : ℝ)*x 1 + (5322935109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489743203/2500000000 : ℝ)^135 ≤ (11805273946269/100000000000000 : ℝ)^103 := by
    have hnat : (489743203 : ℕ)^135*100000000000000^103 ≤ 11805273946269^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489743203 2500000000 11805273946269 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692770703/5000000000 : ℝ)^135 ≤ (22217634522883/50000000000000 : ℝ)^103 := by
    have hnat : (2692770703 : ℕ)^135*50000000000000^103 ≤ 22217634522883^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692770703 5000000000 22217634522883 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5322935109/10000000000 : ℝ)^135 ≤ (43759456988717/100000000000000 : ℝ)^103 := by
    have hnat : (5322935109 : ℕ)^135*100000000000000^103 ≤ 43759456988717^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322935109 10000000000 43759456988717 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489743203/2500000000 : ℝ), (2692770703/5000000000 : ℝ), (5322935109/10000000000 : ℝ)] ![(11805273946269/100000000000000 : ℝ), (22217634522883/50000000000000 : ℝ), (43759456988717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489743203/2500000000 : ℝ)|^135 ≤ (11805273946269/100000000000000 : ℝ)^103
        have hw : |(-489743203/2500000000 : ℝ)|=(489743203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692770703/5000000000 : ℝ)|^135 ≤ (22217634522883/50000000000000 : ℝ)^103
        have hw : |(2692770703/5000000000 : ℝ)|=(2692770703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5322935109/10000000000 : ℝ)|^135 ≤ (43759456988717/100000000000000 : ℝ)^103
        have hw : |(5322935109/10000000000 : ℝ)|=(5322935109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1272122359/10000000000 : ℝ)*x 0 + (-31268147/10000000000 : ℝ)*x 1 + (4740149433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1272122359/10000000000 : ℝ)^135 ≤ (6703849685577/100000000000000 : ℝ)^103 := by
    have hnat : (1272122359 : ℕ)^135*100000000000000^103 ≤ 6703849685577^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272122359 10000000000 6703849685577 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31268147/10000000000 : ℝ)^135 ≤ (5210524619/10000000000000 : ℝ)^103 := by
    have hnat : (31268147 : ℕ)^135*10000000000000^103 ≤ 5210524619^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31268147 10000000000 5210524619 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4740149433/5000000000 : ℝ)^135 ≤ (46622022526033/50000000000000 : ℝ)^103 := by
    have hnat : (4740149433 : ℕ)^135*50000000000000^103 ≤ 46622022526033^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4740149433 5000000000 46622022526033 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1272122359/10000000000 : ℝ), (-31268147/10000000000 : ℝ), (4740149433/5000000000 : ℝ)] ![(6703849685577/100000000000000 : ℝ), (5210524619/10000000000000 : ℝ), (46622022526033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1272122359/10000000000 : ℝ)|^135 ≤ (6703849685577/100000000000000 : ℝ)^103
        have hw : |(1272122359/10000000000 : ℝ)|=(1272122359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31268147/10000000000 : ℝ)|^135 ≤ (5210524619/10000000000000 : ℝ)^103
        have hw : |(-31268147/10000000000 : ℝ)|=(31268147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4740149433/5000000000 : ℝ)|^135 ≤ (46622022526033/50000000000000 : ℝ)^103
        have hw : |(4740149433/5000000000 : ℝ)|=(4740149433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7745650231/10000000000 : ℝ)*x 0 + (866908023/2500000000 : ℝ)*x 1 + (-387365177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7745650231/10000000000 : ℝ)^135 ≤ (71546835127017/100000000000000 : ℝ)^103 := by
    have hnat : (7745650231 : ℕ)^135*100000000000000^103 ≤ 71546835127017^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7745650231 10000000000 71546835127017 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866908023/2500000000 : ℝ)^135 ≤ (4990690578141/20000000000000 : ℝ)^103 := by
    have hnat : (866908023 : ℕ)^135*20000000000000^103 ≤ 4990690578141^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866908023 2500000000 4990690578141 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387365177/5000000000 : ℝ)^135 ≤ (17498559857/500000000000 : ℝ)^103 := by
    have hnat : (387365177 : ℕ)^135*500000000000^103 ≤ 17498559857^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387365177 5000000000 17498559857 500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7745650231/10000000000 : ℝ), (866908023/2500000000 : ℝ), (-387365177/5000000000 : ℝ)] ![(71546835127017/100000000000000 : ℝ), (4990690578141/20000000000000 : ℝ), (17498559857/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7745650231/10000000000 : ℝ)|^135 ≤ (71546835127017/100000000000000 : ℝ)^103
        have hw : |(7745650231/10000000000 : ℝ)|=(7745650231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(866908023/2500000000 : ℝ)|^135 ≤ (4990690578141/20000000000000 : ℝ)^103
        have hw : |(866908023/2500000000 : ℝ)|=(866908023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387365177/5000000000 : ℝ)|^135 ≤ (17498559857/500000000000 : ℝ)^103
        have hw : |(-387365177/5000000000 : ℝ)|=(387365177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4452618791/5000000000 : ℝ)*x 0 + (1846842347/10000000000 : ℝ)*x 1 + (359265123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452618791/5000000000 : ℝ)^135 ≤ (17180325702047/20000000000000 : ℝ)^103 := by
    have hnat : (4452618791 : ℕ)^135*20000000000000^103 ≤ 17180325702047^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452618791 5000000000 17180325702047 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846842347/10000000000 : ℝ)^135 ≤ (1365949173671/12500000000000 : ℝ)^103 := by
    have hnat : (1846842347 : ℕ)^135*12500000000000^103 ≤ 1365949173671^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846842347 10000000000 1365949173671 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359265123/5000000000 : ℝ)^135 ≤ (1585389041783/50000000000000 : ℝ)^103 := by
    have hnat : (359265123 : ℕ)^135*50000000000000^103 ≤ 1585389041783^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359265123 5000000000 1585389041783 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452618791/5000000000 : ℝ), (1846842347/10000000000 : ℝ), (359265123/5000000000 : ℝ)] ![(17180325702047/20000000000000 : ℝ), (1365949173671/12500000000000 : ℝ), (1585389041783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452618791/5000000000 : ℝ)|^135 ≤ (17180325702047/20000000000000 : ℝ)^103
        have hw : |(4452618791/5000000000 : ℝ)|=(4452618791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846842347/10000000000 : ℝ)|^135 ≤ (1365949173671/12500000000000 : ℝ)^103
        have hw : |(1846842347/10000000000 : ℝ)|=(1846842347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(359265123/5000000000 : ℝ)|^135 ≤ (1585389041783/50000000000000 : ℝ)^103
        have hw : |(359265123/5000000000 : ℝ)|=(359265123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-616837607/5000000000 : ℝ)*x 0 + (513765819/625000000 : ℝ)*x 1 + (124778713/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (616837607/5000000000 : ℝ)^135 ≤ (1609887312391/25000000000000 : ℝ)^103 := by
    have hnat : (616837607 : ℕ)^135*25000000000000^103 ≤ 1609887312391^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616837607 5000000000 1609887312391 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513765819/625000000 : ℝ)^135 ≤ (77346693656549/100000000000000 : ℝ)^103 := by
    have hnat : (513765819 : ℕ)^135*100000000000000^103 ≤ 77346693656549^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513765819 625000000 77346693656549 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124778713/500000000 : ℝ)^135 ≤ (3242751414967/20000000000000 : ℝ)^103 := by
    have hnat : (124778713 : ℕ)^135*20000000000000^103 ≤ 3242751414967^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124778713 500000000 3242751414967 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-616837607/5000000000 : ℝ), (513765819/625000000 : ℝ), (124778713/500000000 : ℝ)] ![(1609887312391/25000000000000 : ℝ), (77346693656549/100000000000000 : ℝ), (3242751414967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-616837607/5000000000 : ℝ)|^135 ≤ (1609887312391/25000000000000 : ℝ)^103
        have hw : |(-616837607/5000000000 : ℝ)|=(616837607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513765819/625000000 : ℝ)|^135 ≤ (77346693656549/100000000000000 : ℝ)^103
        have hw : |(513765819/625000000 : ℝ)|=(513765819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124778713/500000000 : ℝ)|^135 ≤ (3242751414967/20000000000000 : ℝ)^103
        have hw : |(124778713/500000000 : ℝ)|=(124778713/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7906786823/10000000000 : ℝ)*x 0 + (-368251/1250000000 : ℝ)*x 1 + (3629769193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7906786823/10000000000 : ℝ)^135 ≤ (14700791374663/20000000000000 : ℝ)^103 := by
    have hnat : (7906786823 : ℕ)^135*20000000000000^103 ≤ 14700791374663^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7906786823 10000000000 14700791374663 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368251/1250000000 : ℝ)^135 ≤ (2356659769/100000000000000 : ℝ)^103 := by
    have hnat : (368251 : ℕ)^135*100000000000000^103 ≤ 2356659769^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368251 1250000000 2356659769 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3629769193/10000000000 : ℝ)^135 ≤ (26493686449903/100000000000000 : ℝ)^103 := by
    have hnat : (3629769193 : ℕ)^135*100000000000000^103 ≤ 26493686449903^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629769193 10000000000 26493686449903 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7906786823/10000000000 : ℝ), (-368251/1250000000 : ℝ), (3629769193/10000000000 : ℝ)] ![(14700791374663/20000000000000 : ℝ), (2356659769/100000000000000 : ℝ), (26493686449903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7906786823/10000000000 : ℝ)|^135 ≤ (14700791374663/20000000000000 : ℝ)^103
        have hw : |(7906786823/10000000000 : ℝ)|=(7906786823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-368251/1250000000 : ℝ)|^135 ≤ (2356659769/100000000000000 : ℝ)^103
        have hw : |(-368251/1250000000 : ℝ)|=(368251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3629769193/10000000000 : ℝ)|^135 ≤ (26493686449903/100000000000000 : ℝ)^103
        have hw : |(3629769193/10000000000 : ℝ)|=(3629769193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4274477/39062500 : ℝ)*x 0 + (8869179027/10000000000 : ℝ)*x 1 + (-1599550271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274477/39062500 : ℝ)^135 ≤ (171968167253/3125000000000 : ℝ)^103 := by
    have hnat : (4274477 : ℕ)^135*3125000000000^103 ≤ 171968167253^103*39062500^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274477 39062500 171968167253 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8869179027/10000000000 : ℝ)^135 ≤ (21361506202983/25000000000000 : ℝ)^103 := by
    have hnat : (8869179027 : ℕ)^135*25000000000000^103 ≤ 21361506202983^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8869179027 10000000000 21361506202983 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1599550271/10000000000 : ℝ)^135 ≤ (45254969113/500000000000 : ℝ)^103 := by
    have hnat : (1599550271 : ℕ)^135*500000000000^103 ≤ 45254969113^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599550271 10000000000 45254969113 500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274477/39062500 : ℝ), (8869179027/10000000000 : ℝ), (-1599550271/10000000000 : ℝ)] ![(171968167253/3125000000000 : ℝ), (21361506202983/25000000000000 : ℝ), (45254969113/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274477/39062500 : ℝ)|^135 ≤ (171968167253/3125000000000 : ℝ)^103
        have hw : |(4274477/39062500 : ℝ)|=(4274477/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8869179027/10000000000 : ℝ)|^135 ≤ (21361506202983/25000000000000 : ℝ)^103
        have hw : |(8869179027/10000000000 : ℝ)|=(8869179027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1599550271/10000000000 : ℝ)|^135 ≤ (45254969113/500000000000 : ℝ)^103
        have hw : |(-1599550271/10000000000 : ℝ)|=(1599550271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s1_s1_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1685304211/2000000000 : ℝ)*x 0 + (264691231/1250000000 : ℝ)*x 1 + (1318579757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1685304211/2000000000 : ℝ)^135 ≤ (39950181849503/50000000000000 : ℝ)^103 := by
    have hnat : (1685304211 : ℕ)^135*50000000000000^103 ≤ 39950181849503^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685304211 2000000000 39950181849503 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264691231/1250000000 : ℝ)^135 ≤ (3268274556011/25000000000000 : ℝ)^103 := by
    have hnat : (264691231 : ℕ)^135*25000000000000^103 ≤ 3268274556011^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264691231 1250000000 3268274556011 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318579757/10000000000 : ℝ)^135 ≤ (1405307613449/20000000000000 : ℝ)^103 := by
    have hnat : (1318579757 : ℕ)^135*20000000000000^103 ≤ 1405307613449^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318579757 10000000000 1405307613449 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1685304211/2000000000 : ℝ), (264691231/1250000000 : ℝ), (1318579757/10000000000 : ℝ)] ![(39950181849503/50000000000000 : ℝ), (3268274556011/25000000000000 : ℝ), (1405307613449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1685304211/2000000000 : ℝ)|^135 ≤ (39950181849503/50000000000000 : ℝ)^103
        have hw : |(1685304211/2000000000 : ℝ)|=(1685304211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264691231/1250000000 : ℝ)|^135 ≤ (3268274556011/25000000000000 : ℝ)^103
        have hw : |(264691231/1250000000 : ℝ)|=(264691231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318579757/10000000000 : ℝ)|^135 ≤ (1405307613449/20000000000000 : ℝ)^103
        have hw : |(1318579757/10000000000 : ℝ)|=(1318579757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306055_s1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((47147/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47147/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47163/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47163/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18761/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18761/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((88451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43833/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43833/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5471/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5471/6250 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (47147/50000 : ℝ) ^ (67/16 : ℝ) ≤ (39095070615855573069/50000000000000000000 : ℝ) := by
    have hpowers : (47147/50000 : ℝ)^67 ≤ (39095070615855573069/50000000000000000000 : ℝ)^16 := by
      have hnat : (47147 : ℕ)^67*50000000000000000000^16 ≤ 39095070615855573069^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47147 50000 39095070615855573069 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47147/50000 : ℝ)) (X := (39095070615855573069/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (89095070615855573069/50000000000000000000 : ℝ) ≤ (2869805921499029/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (89095070615855573069/50000000000000000000 : ℝ)^16 ≤ (2869805921499029/2500000000000000 : ℝ)^67 := by
      have hnat : (89095070615855573069 : ℕ)^16*2500000000000000^67 ≤ 2869805921499029^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89095070615855573069 50000000000000000000 2869805921499029 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2869805921499029/2500000000000000 : ℝ)) (X := (89095070615855573069/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (64095070615855573069/25000000000000000000 : ℝ) ≤ (2504229252990897/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (64095070615855573069/25000000000000000000 : ℝ)^16 ≤ (2504229252990897/2000000000000000 : ℝ)^67 := by
      have hnat : (64095070615855573069 : ℕ)^16*2000000000000000^67 ≤ 2504229252990897^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64095070615855573069 25000000000000000000 2504229252990897 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504229252990897/2000000000000000 : ℝ)) (X := (64095070615855573069/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(369805921499029/2357350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1041922578958369/9429400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (47147/50000 : ℝ)) (alpha := (369805921499029/2357350000000000 : ℝ)) (beta := (1041922578958369/9429400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (47147/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(369805921499029/2357350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1041922578958369/9429400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (47163/50000 : ℝ) ^ (67/16 : ℝ) ≤ (19575329089061995933/25000000000000000000 : ℝ) := by
    have hpowers : (47163/50000 : ℝ)^67 ≤ (19575329089061995933/25000000000000000000 : ℝ)^16 := by
      have hnat : (47163 : ℕ)^67*25000000000000000000^16 ≤ 19575329089061995933^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47163 50000 19575329089061995933 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47163/50000 : ℝ)) (X := (19575329089061995933/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (44575329089061995933/25000000000000000000 : ℝ) ≤ (11480933616852643/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (44575329089061995933/25000000000000000000 : ℝ)^16 ≤ (11480933616852643/10000000000000000 : ℝ)^67 := by
      have hnat : (44575329089061995933 : ℕ)^16*10000000000000000^67 ≤ 11480933616852643^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44575329089061995933 25000000000000000000 11480933616852643 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11480933616852643/10000000000000000 : ℝ)) (X := (44575329089061995933/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (32075329089061995933/12500000000000000000 : ℝ) ≤ (1252373864676147/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (32075329089061995933/12500000000000000000 : ℝ)^16 ≤ (1252373864676147/1000000000000000 : ℝ)^67 := by
      have hnat : (32075329089061995933 : ℕ)^16*1000000000000000^67 ≤ 1252373864676147^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32075329089061995933 12500000000000000000 1252373864676147 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252373864676147/1000000000000000 : ℝ)) (X := (32075329089061995933/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(493644538950881/3144200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1042805029908827/9432600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (47163/50000 : ℝ)) (alpha := (493644538950881/3144200000000000 : ℝ)) (beta := (1042805029908827/9432600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (47163/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(493644538950881/3144200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1042805029908827/9432600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (18761/20000 : ℝ) ^ (67/16 : ℝ) ≤ (9563268226818438819/12500000000000000000 : ℝ) := by
    have hpowers : (18761/20000 : ℝ)^67 ≤ (9563268226818438819/12500000000000000000 : ℝ)^16 := by
      have hnat : (18761 : ℕ)^67*12500000000000000000^16 ≤ 9563268226818438819^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18761 20000 9563268226818438819 12500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18761/20000 : ℝ)) (X := (9563268226818438819/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (22063268226818438819/12500000000000000000 : ℝ) ≤ (11453223113260413/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (22063268226818438819/12500000000000000000 : ℝ)^16 ≤ (11453223113260413/10000000000000000 : ℝ)^67 := by
      have hnat : (22063268226818438819 : ℕ)^16*10000000000000000^67 ≤ 11453223113260413^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22063268226818438819 12500000000000000000 11453223113260413 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11453223113260413/10000000000000000 : ℝ)) (X := (22063268226818438819/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (15813268226818438819/6250000000000000000 : ℝ) ≤ (3120416993730653/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (15813268226818438819/6250000000000000000 : ℝ)^16 ≤ (3120416993730653/2500000000000000 : ℝ)^67 := by
      have hnat : (15813268226818438819 : ℕ)^16*2500000000000000^67 ≤ 3120416993730653^67*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15813268226818438819 6250000000000000000 3120416993730653 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3120416993730653/2500000000000000 : ℝ)) (X := (15813268226818438819/6250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1453223113260413/9380500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1028444861662199/9380500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (18761/20000 : ℝ)) (alpha := (1453223113260413/9380500000000000 : ℝ)) (beta := (1028444861662199/9380500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (18761/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1453223113260413/9380500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1028444861662199/9380500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_6 : ((6646717161/10000000000 : ℝ)*X 0 0+(3788998813/10000000000 : ℝ)*X 0 1+(2161134179/10000000000 : ℝ)*X 0 2+(6646717161/10000000000 : ℝ)*X 1 0+(3788998813/10000000000 : ℝ)*X 1 1+(2161134179/10000000000 : ℝ)*X 1 2+(6646717161/10000000000 : ℝ)*X 2 0+(3788998813/10000000000 : ℝ)*X 2 1+(2161134179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2055188427/5000000000 : ℝ)*X 0 0+(4368918349/10000000000 : ℝ)*X 0 1+(898520923/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((567728039/2500000000 : ℝ)*X 1 0+(409631/2000000000 : ℝ)*X 1 1+(8886955333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((946704129/5000000000 : ℝ)*X 2 0+(8846735711/10000000000 : ℝ)*X 2 1+(-782726729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3693400583/10000000000 : ℝ)*X 0 0+(302571529/400000000 : ℝ)*X 0 1+(780981597/10000000000 : ℝ)*X 0 2+(3693400583/10000000000 : ℝ)*X 1 0+(302571529/400000000 : ℝ)*X 1 1+(780981597/10000000000 : ℝ)*X 1 2+(3693400583/10000000000 : ℝ)*X 2 0+(302571529/400000000 : ℝ)*X 2 1+(780981597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-489743203/2500000000 : ℝ)*X 0 0+(2692770703/5000000000 : ℝ)*X 0 1+(5322935109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1272122359/10000000000 : ℝ)*X 1 0+(-31268147/10000000000 : ℝ)*X 1 1+(4740149433/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7745650231/10000000000 : ℝ)*X 2 0+(866908023/2500000000 : ℝ)*X 2 1+(-387365177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4452618791/5000000000 : ℝ)*X 0 0+(1846842347/10000000000 : ℝ)*X 0 1+(359265123/5000000000 : ℝ)*X 0 2+(4452618791/5000000000 : ℝ)*X 1 0+(1846842347/10000000000 : ℝ)*X 1 1+(359265123/5000000000 : ℝ)*X 1 2+(4452618791/5000000000 : ℝ)*X 2 0+(1846842347/10000000000 : ℝ)*X 2 1+(359265123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-616837607/5000000000 : ℝ)*X 0 0+(513765819/625000000 : ℝ)*X 0 1+(124778713/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7906786823/10000000000 : ℝ)*X 1 0+(-368251/1250000000 : ℝ)*X 1 1+(3629769193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4274477/39062500 : ℝ)*X 2 0+(8869179027/10000000000 : ℝ)*X 2 1+(-1599550271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1685304211/2000000000 : ℝ)*X 0 0+(264691231/1250000000 : ℝ)*X 0 1+(1318579757/10000000000 : ℝ)*X 0 2+(1685304211/2000000000 : ℝ)*X 1 0+(264691231/1250000000 : ℝ)*X 1 1+(1318579757/10000000000 : ℝ)*X 1 2+(1685304211/2000000000 : ℝ)*X 2 0+(264691231/1250000000 : ℝ)*X 2 1+(1318579757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((88451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11170353343881427881981115119199/869100964631687500000000000000000000 : ℝ) := by norm_num
    linear_combination (706434839687/1000000000000 : ℝ)*(base7) + (10983/125000000000 : ℝ)*(base23) + (34058018899/1000000000000 : ℝ)*(base43) + (174687/200000000000 : ℝ)*(base49) + (966537163119/1000000000000 : ℝ)*(base53) + (802169379013/500000000000 : ℝ)*(major_s1_0) + (196285092391/125000000000 : ℝ)*(major_s1_1) + (159450398727/250000000000 : ℝ)*(major_s1_2) + (729548954313/1000000000000 : ℝ)*(sp_s1_7) + (381819458217/500000000000 : ℝ)*(sp_s1_8) + (1696117972791/1000000000000 : ℝ)*(sp_s1_9) + (1746956520013/1000000000000 : ℝ)*(sp_s1_13) + (1279977/250000000000 : ℝ)*(sp_s1_14) + (5364663/200000000000 : ℝ)*(sp_s1_21) + (41620867213/40000000000 : ℝ)*(f.failure) + (1730176079553/1000000000000 : ℝ)*(f.sum) + (97917421607932023/73735420250000000000000000000000 : ℝ)*base62 + (73012789156613/586281250000000000000000000 : ℝ)*base64 + (943744807094983/1179075000000000000000000000 : ℝ)*base67 + (1460281257820573/4690250000000000000000000000 : ℝ)*base68 + (33266713000606227793/221131216750000000000000000000000 : ℝ)*base70 + (3718459286673787/4714700000000000000000000000 : ℝ)*base73 + (424947575325543/786050000000000000000000000 : ℝ)*base74 + (73506896200357/294668750000000000000000000 : ℝ)*base76 + (2696961415598500703/8894375844000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (191/2000000000000000 : ℝ)*base86 + (2191/2000000000000000 : ℝ)*base88 + (2191/2000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43833/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43833/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (252937358063458673246473329/55282804187500000000000000000000 : ℝ) := by norm_num
    linear_combination (44903783911/62500000000 : ℝ)*(base7) + (27799207401/1000000000000 : ℝ)*(base34) + (27007/1000000000000 : ℝ)*(base40) + (165835852683/200000000000 : ℝ)*(base53) + (147469246659/100000000000 : ℝ)*(major_s1_0) + (150249167399/100000000000 : ℝ)*(major_s1_1) + (42082025661/62500000000 : ℝ)*(major_s1_2) + (28551993/500000000000 : ℝ)*(sp_s1_8) + (364045686249/500000000000 : ℝ)*(sp_s1_14) + (755847297767/1000000000000 : ℝ)*(sp_s1_15) + (99067729073/62500000000 : ℝ)*(sp_s1_16) + (104069756477/62500000000 : ℝ)*(sp_s1_20) + (6910927/500000000000 : ℝ)*(sp_s1_21) + (2444411/200000000000 : ℝ)*(sp_s1_27) + (60904186907/62500000000 : ℝ)*(f.failure) + (99067729073/62500000000 : ℝ)*(f.sum) + (57589771045199612627/147470840500000000000000000000000 : ℝ)*base62 + (32144086168153/1172562500000000000000000000 : ℝ)*base65 + (677633570499173/943260000000000000000000000 : ℝ)*base67 + (544818026460747/2345125000000000000000000000 : ℝ)*base69 + (76337680733540667539/221131216750000000000000000000000 : ℝ)*base71 + (425380246043073/942940000000000000000000000 : ℝ)*base73 + (45630934197/503072000000000000000000 : ℝ)*base75 + (5706350399211/235735000000000000000000000 : ℝ)*base77 + (2519922431604010157/11117969805000000000000000000000 : ℝ)*base78 + (131/781250000000000 : ℝ)*base86 + (2601/3125000000000000 : ℝ)*base89 + (131/781250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5471/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5471/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (110790304774736409/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (452451419059/500000000000 : ℝ)*(base7) + (14473600829/40000000000 : ℝ)*(base43) + (8409810357/250000000000 : ℝ)*(base50) + (1480121288167/1000000000000 : ℝ)*(major_s1_0) + (559140633721/500000000000 : ℝ)*(major_s1_1) + (1480121288167/1000000000000 : ℝ)*(major_s1_2) + (5968837/250000000000 : ℝ)*(sp_s1_6) + (4417/6250000000 : ℝ)*(sp_s1_7) + (56519119/1000000000000 : ℝ)*(sp_s1_9) + (100122863/1000000000000 : ℝ)*(sp_s1_20) + (21548364097/20000000000 : ℝ)*(sp_s1_21) + (719629466147/500000000000 : ℝ)*(sp_s1_22) + (1077362392451/1000000000000 : ℝ)*(sp_s1_23) + (932368564677/500000000000 : ℝ)*(sp_s1_27) + (959958289447/1000000000000 : ℝ)*(f.failure) + (719629466147/500000000000 : ℝ)*(f.sum) + (390151245069790837/18433855062500000000000000000000 : ℝ)*base63 + (7268278251129617/9380500000000000000000000000 : ℝ)*base64 + (2108790440535107/4716300000000000000000000000 : ℝ)*base66 + (1644596836291329/9380500000000000000000000000 : ℝ)*base68 + (21800137549888879731/442262433500000000000000000000000 : ℝ)*base71 + (1542524793651777/9429400000000000000000000000 : ℝ)*base72 + (798279263263179/1572100000000000000000000000 : ℝ)*base74 + (1117786748443481/1178675000000000000000000000 : ℝ)*base76 + (50190976598113737931/444718792200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (12429/50000000000000000 : ℝ)*base86 + (12429/50000000000000000 : ℝ)*base88 + (12429/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((47147/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47147/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47163/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47163/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18761/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18761/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((88451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43833/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43833/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5471/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5471/6250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306055_s1 p hpa hpb X hX hprev0

#print axioms solution
