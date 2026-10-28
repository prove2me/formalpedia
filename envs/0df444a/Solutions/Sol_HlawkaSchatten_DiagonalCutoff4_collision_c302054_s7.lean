-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302054_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:41.952625+00:00
-- url     : https://prove2.me/submissions/02779032-5d0b-4d75-a9b6-aed8206c6c0c

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
theorem collision_support_c302054_s7_s7_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-130525913/625000000 : ℝ)*x 0 + (1145720869/2500000000 : ℝ)*x 1 + (-378859497/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130525913/625000000 : ℝ)^33 ≤ (12651967670457/100000000000000 : ℝ)^25 := by
    have hnat : (130525913 : ℕ)^33*100000000000000^25 ≤ 12651967670457^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130525913 625000000 12651967670457 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145720869/2500000000 : ℝ)^33 ≤ (35702878820071/100000000000000 : ℝ)^25 := by
    have hnat : (1145720869 : ℕ)^33*100000000000000^25 ≤ 35702878820071^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145720869 2500000000 35702878820071 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378859497/625000000 : ℝ)^33 ≤ (51645153491221/100000000000000 : ℝ)^25 := by
    have hnat : (378859497 : ℕ)^33*100000000000000^25 ≤ 51645153491221^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378859497 625000000 51645153491221 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130525913/625000000 : ℝ), (1145720869/2500000000 : ℝ), (-378859497/625000000 : ℝ)] ![(12651967670457/100000000000000 : ℝ), (35702878820071/100000000000000 : ℝ), (51645153491221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130525913/625000000 : ℝ)|^33 ≤ (12651967670457/100000000000000 : ℝ)^25
        have hw : |(-130525913/625000000 : ℝ)|=(130525913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1145720869/2500000000 : ℝ)|^33 ≤ (35702878820071/100000000000000 : ℝ)^25
        have hw : |(1145720869/2500000000 : ℝ)|=(1145720869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378859497/625000000 : ℝ)|^33 ≤ (51645153491221/100000000000000 : ℝ)^25
        have hw : |(-378859497/625000000 : ℝ)|=(378859497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5416790761/10000000000 : ℝ)*x 0 + (-73110879/250000000 : ℝ)*x 1 + (-573425907/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416790761/10000000000 : ℝ)^33 ≤ (44518397124487/100000000000000 : ℝ)^25 := by
    have hnat : (5416790761 : ℕ)^33*100000000000000^25 ≤ 44518397124487^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416790761 10000000000 44518397124487 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73110879/250000000 : ℝ)^33 ≤ (1973219668163/10000000000000 : ℝ)^25 := by
    have hnat : (73110879 : ℕ)^33*10000000000000^25 ≤ 1973219668163^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73110879 250000000 1973219668163 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573425907/1250000000 : ℝ)^33 ≤ (8937351544681/25000000000000 : ℝ)^25 := by
    have hnat : (573425907 : ℕ)^33*25000000000000^25 ≤ 8937351544681^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573425907 1250000000 8937351544681 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416790761/10000000000 : ℝ), (-73110879/250000000 : ℝ), (-573425907/1250000000 : ℝ)] ![(44518397124487/100000000000000 : ℝ), (1973219668163/10000000000000 : ℝ), (8937351544681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416790761/10000000000 : ℝ)|^33 ≤ (44518397124487/100000000000000 : ℝ)^25
        have hw : |(5416790761/10000000000 : ℝ)|=(5416790761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-73110879/250000000 : ℝ)|^33 ≤ (1973219668163/10000000000000 : ℝ)^25
        have hw : |(-73110879/250000000 : ℝ)|=(73110879/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-573425907/1250000000 : ℝ)|^33 ≤ (8937351544681/25000000000000 : ℝ)^25
        have hw : |(-573425907/1250000000 : ℝ)|=(573425907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1002225367/2000000000 : ℝ)*x 0 + (2504822893/5000000000 : ℝ)*x 1 + (1458909247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002225367/2000000000 : ℝ)^33 ≤ (40171192266037/100000000000000 : ℝ)^25 := by
    have hnat : (1002225367 : ℕ)^33*100000000000000^25 ≤ 40171192266037^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002225367 2000000000 40171192266037 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2504822893/5000000000 : ℝ)^33 ≤ (40155521069907/100000000000000 : ℝ)^25 := by
    have hnat : (2504822893 : ℕ)^33*100000000000000^25 ≤ 40155521069907^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504822893 5000000000 40155521069907 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458909247/5000000000 : ℝ)^33 ≤ (19673286650009/100000000000000 : ℝ)^25 := by
    have hnat : (1458909247 : ℕ)^33*100000000000000^25 ≤ 19673286650009^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458909247 5000000000 19673286650009 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1002225367/2000000000 : ℝ), (2504822893/5000000000 : ℝ), (1458909247/5000000000 : ℝ)] ![(40171192266037/100000000000000 : ℝ), (40155521069907/100000000000000 : ℝ), (19673286650009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1002225367/2000000000 : ℝ)|^33 ≤ (40171192266037/100000000000000 : ℝ)^25
        have hw : |(1002225367/2000000000 : ℝ)|=(1002225367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2504822893/5000000000 : ℝ)|^33 ≤ (40155521069907/100000000000000 : ℝ)^25
        have hw : |(2504822893/5000000000 : ℝ)|=(2504822893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458909247/5000000000 : ℝ)|^33 ≤ (19673286650009/100000000000000 : ℝ)^25
        have hw : |(1458909247/5000000000 : ℝ)|=(1458909247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5008266839/10000000000 : ℝ)*x 0 + (625876607/1250000000 : ℝ)*x 1 + (-2924346059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5008266839/10000000000 : ℝ)^33 ≤ (40140931562687/100000000000000 : ℝ)^25 := by
    have hnat : (5008266839 : ℕ)^33*100000000000000^25 ≤ 40140931562687^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008266839 10000000000 40140931562687 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625876607/1250000000 : ℝ)^33 ≤ (20063832656491/50000000000000 : ℝ)^25 := by
    have hnat : (625876607 : ℕ)^33*50000000000000^25 ≤ 20063832656491^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625876607 1250000000 20063832656491 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2924346059/10000000000 : ℝ)^33 ≤ (9865701553449/50000000000000 : ℝ)^25 := by
    have hnat : (2924346059 : ℕ)^33*50000000000000^25 ≤ 9865701553449^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2924346059 10000000000 9865701553449 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5008266839/10000000000 : ℝ), (625876607/1250000000 : ℝ), (-2924346059/10000000000 : ℝ)] ![(40140931562687/100000000000000 : ℝ), (20063832656491/50000000000000 : ℝ), (9865701553449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5008266839/10000000000 : ℝ)|^33 ≤ (40140931562687/100000000000000 : ℝ)^25
        have hw : |(5008266839/10000000000 : ℝ)|=(5008266839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625876607/1250000000 : ℝ)|^33 ≤ (20063832656491/50000000000000 : ℝ)^25
        have hw : |(625876607/1250000000 : ℝ)|=(625876607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2924346059/10000000000 : ℝ)|^33 ≤ (9865701553449/50000000000000 : ℝ)^25
        have hw : |(-2924346059/10000000000 : ℝ)|=(2924346059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2081648217/10000000000 : ℝ)*x 0 + (4538645393/10000000000 : ℝ)*x 1 + (-3053447749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081648217/10000000000 : ℝ)^33 ≤ (12597886384149/100000000000000 : ℝ)^25 := by
    have hnat : (2081648217 : ℕ)^33*100000000000000^25 ≤ 12597886384149^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081648217 10000000000 12597886384149 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538645393/10000000000 : ℝ)^33 ≤ (35248663367409/100000000000000 : ℝ)^25 := by
    have hnat : (4538645393 : ℕ)^33*100000000000000^25 ≤ 35248663367409^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538645393 10000000000 35248663367409 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3053447749/5000000000 : ℝ)^33 ≤ (52153450231233/100000000000000 : ℝ)^25 := by
    have hnat : (3053447749 : ℕ)^33*100000000000000^25 ≤ 52153450231233^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3053447749 5000000000 52153450231233 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2081648217/10000000000 : ℝ), (4538645393/10000000000 : ℝ), (-3053447749/5000000000 : ℝ)] ![(12597886384149/100000000000000 : ℝ), (35248663367409/100000000000000 : ℝ), (52153450231233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2081648217/10000000000 : ℝ)|^33 ≤ (12597886384149/100000000000000 : ℝ)^25
        have hw : |(-2081648217/10000000000 : ℝ)|=(2081648217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538645393/10000000000 : ℝ)|^33 ≤ (35248663367409/100000000000000 : ℝ)^25
        have hw : |(4538645393/10000000000 : ℝ)|=(4538645393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3053447749/5000000000 : ℝ)|^33 ≤ (52153450231233/100000000000000 : ℝ)^25
        have hw : |(-3053447749/5000000000 : ℝ)|=(3053447749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5406416511/10000000000 : ℝ)*x 0 + (-357097803/1250000000 : ℝ)*x 1 + (-582067049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406416511/10000000000 : ℝ)^33 ≤ (11101471534033/25000000000000 : ℝ)^25 := by
    have hnat : (5406416511 : ℕ)^33*25000000000000^25 ≤ 11101471534033^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406416511 10000000000 11101471534033 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357097803/1250000000 : ℝ)^33 ≤ (19131889247849/100000000000000 : ℝ)^25 := by
    have hnat : (357097803 : ℕ)^33*100000000000000^25 ≤ 19131889247849^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357097803 1250000000 19131889247849 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582067049/1250000000 : ℝ)^33 ≤ (3646222459783/10000000000000 : ℝ)^25 := by
    have hnat : (582067049 : ℕ)^33*10000000000000^25 ≤ 3646222459783^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582067049 1250000000 3646222459783 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406416511/10000000000 : ℝ), (-357097803/1250000000 : ℝ), (-582067049/1250000000 : ℝ)] ![(11101471534033/25000000000000 : ℝ), (19131889247849/100000000000000 : ℝ), (3646222459783/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406416511/10000000000 : ℝ)|^33 ≤ (11101471534033/25000000000000 : ℝ)^25
        have hw : |(5406416511/10000000000 : ℝ)|=(5406416511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-357097803/1250000000 : ℝ)|^33 ≤ (19131889247849/100000000000000 : ℝ)^25
        have hw : |(-357097803/1250000000 : ℝ)|=(357097803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-582067049/1250000000 : ℝ)|^33 ≤ (3646222459783/10000000000000 : ℝ)^25
        have hw : |(-582067049/1250000000 : ℝ)|=(582067049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (998907731/2000000000 : ℝ)*x 0 + (5083767137/10000000000 : ℝ)*x 1 + (2848943329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998907731/2000000000 : ℝ)^33 ≤ (9998938760987/25000000000000 : ℝ)^25 := by
    have hnat : (998907731 : ℕ)^33*25000000000000^25 ≤ 9998938760987^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998907731 2000000000 9998938760987 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083767137/10000000000 : ℝ)^33 ≤ (40941623217523/100000000000000 : ℝ)^25 := by
    have hnat : (5083767137 : ℕ)^33*100000000000000^25 ≤ 40941623217523^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083767137 10000000000 40941623217523 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2848943329/10000000000 : ℝ)^33 ≤ (19062621715481/100000000000000 : ℝ)^25 := by
    have hnat : (2848943329 : ℕ)^33*100000000000000^25 ≤ 19062621715481^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848943329 10000000000 19062621715481 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(998907731/2000000000 : ℝ), (5083767137/10000000000 : ℝ), (2848943329/10000000000 : ℝ)] ![(9998938760987/25000000000000 : ℝ), (40941623217523/100000000000000 : ℝ), (19062621715481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(998907731/2000000000 : ℝ)|^33 ≤ (9998938760987/25000000000000 : ℝ)^25
        have hw : |(998907731/2000000000 : ℝ)|=(998907731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083767137/10000000000 : ℝ)|^33 ≤ (40941623217523/100000000000000 : ℝ)^25
        have hw : |(5083767137/10000000000 : ℝ)|=(5083767137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2848943329/10000000000 : ℝ)|^33 ≤ (19062621715481/100000000000000 : ℝ)^25
        have hw : |(2848943329/10000000000 : ℝ)|=(2848943329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5007003837/10000000000 : ℝ)*x 0 + (5082764807/10000000000 : ℝ)*x 1 + (-708803719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5007003837/10000000000 : ℝ)^33 ≤ (40127569902217/100000000000000 : ℝ)^25 := by
    have hnat : (5007003837 : ℕ)^33*100000000000000^25 ≤ 40127569902217^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007003837 10000000000 40127569902217 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082764807/10000000000 : ℝ)^33 ≤ (2046548414663/5000000000000 : ℝ)^25 := by
    have hnat : (5082764807 : ℕ)^33*5000000000000^25 ≤ 2046548414663^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082764807 10000000000 2046548414663 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708803719/2500000000 : ℝ)^33 ≤ (59192068081/312500000000 : ℝ)^25 := by
    have hnat : (708803719 : ℕ)^33*312500000000^25 ≤ 59192068081^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708803719 2500000000 59192068081 312500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5007003837/10000000000 : ℝ), (5082764807/10000000000 : ℝ), (-708803719/2500000000 : ℝ)] ![(40127569902217/100000000000000 : ℝ), (2046548414663/5000000000000 : ℝ), (59192068081/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5007003837/10000000000 : ℝ)|^33 ≤ (40127569902217/100000000000000 : ℝ)^25
        have hw : |(5007003837/10000000000 : ℝ)|=(5007003837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082764807/10000000000 : ℝ)|^33 ≤ (2046548414663/5000000000000 : ℝ)^25
        have hw : |(5082764807/10000000000 : ℝ)|=(5082764807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-708803719/2500000000 : ℝ)|^33 ≤ (59192068081/312500000000 : ℝ)^25
        have hw : |(-708803719/2500000000 : ℝ)|=(708803719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029590249/10000000000 : ℝ)*x 0 + (286447213/625000000 : ℝ)*x 1 + (-6103096527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029590249/10000000000 : ℝ)^33 ≤ (12183695751121/100000000000000 : ℝ)^25 := by
    have hnat : (2029590249 : ℕ)^33*100000000000000^25 ≤ 12183695751121^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029590249 10000000000 12183695751121 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286447213/625000000 : ℝ)^33 ≤ (35705675242597/100000000000000 : ℝ)^25 := by
    have hnat : (286447213 : ℕ)^33*100000000000000^25 ≤ 35705675242597^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286447213 625000000 35705675242597 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6103096527/10000000000 : ℝ)^33 ≤ (1302765724801/2500000000000 : ℝ)^25 := by
    have hnat : (6103096527 : ℕ)^33*2500000000000^25 ≤ 1302765724801^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6103096527 10000000000 1302765724801 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029590249/10000000000 : ℝ), (286447213/625000000 : ℝ), (-6103096527/10000000000 : ℝ)] ![(12183695751121/100000000000000 : ℝ), (35705675242597/100000000000000 : ℝ), (1302765724801/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029590249/10000000000 : ℝ)|^33 ≤ (12183695751121/100000000000000 : ℝ)^25
        have hw : |(-2029590249/10000000000 : ℝ)|=(2029590249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(286447213/625000000 : ℝ)|^33 ≤ (35705675242597/100000000000000 : ℝ)^25
        have hw : |(286447213/625000000 : ℝ)|=(286447213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6103096527/10000000000 : ℝ)|^33 ≤ (1302765724801/2500000000000 : ℝ)^25
        have hw : |(-6103096527/10000000000 : ℝ)|=(6103096527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5364038887/10000000000 : ℝ)*x 0 + (-181624391/625000000 : ℝ)*x 1 + (-4658730729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364038887/10000000000 : ℝ)^33 ≤ (43947009872563/100000000000000 : ℝ)^25 := by
    have hnat : (5364038887 : ℕ)^33*100000000000000^25 ≤ 43947009872563^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364038887 10000000000 43947009872563 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181624391/625000000 : ℝ)^33 ≤ (19568083051397/100000000000000 : ℝ)^25 := by
    have hnat : (181624391 : ℕ)^33*100000000000000^25 ≤ 19568083051397^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181624391 625000000 19568083051397 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4658730729/10000000000 : ℝ)^33 ≤ (18242453529027/50000000000000 : ℝ)^25 := by
    have hnat : (4658730729 : ℕ)^33*50000000000000^25 ≤ 18242453529027^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4658730729 10000000000 18242453529027 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364038887/10000000000 : ℝ), (-181624391/625000000 : ℝ), (-4658730729/10000000000 : ℝ)] ![(43947009872563/100000000000000 : ℝ), (19568083051397/100000000000000 : ℝ), (18242453529027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364038887/10000000000 : ℝ)|^33 ≤ (43947009872563/100000000000000 : ℝ)^25
        have hw : |(5364038887/10000000000 : ℝ)|=(5364038887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-181624391/625000000 : ℝ)|^33 ≤ (19568083051397/100000000000000 : ℝ)^25
        have hw : |(-181624391/625000000 : ℝ)|=(181624391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4658730729/10000000000 : ℝ)|^33 ≤ (18242453529027/50000000000000 : ℝ)^25
        have hw : |(-4658730729/10000000000 : ℝ)|=(4658730729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2543216513/5000000000 : ℝ)*x 0 + (4993690499/10000000000 : ℝ)*x 1 + (142337459/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2543216513/5000000000 : ℝ)^33 ≤ (40969965305013/100000000000000 : ℝ)^25 := by
    have hnat : (2543216513 : ℕ)^33*100000000000000^25 ≤ 40969965305013^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543216513 5000000000 40969965305013 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993690499/10000000000 : ℝ)^33 ≤ (39986789918099/100000000000000 : ℝ)^25 := by
    have hnat : (4993690499 : ℕ)^33*100000000000000^25 ≤ 39986789918099^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993690499 10000000000 39986789918099 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142337459/500000000 : ℝ)^33 ≤ (297550699517/1562500000000 : ℝ)^25 := by
    have hnat : (142337459 : ℕ)^33*1562500000000^25 ≤ 297550699517^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142337459 500000000 297550699517 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2543216513/5000000000 : ℝ), (4993690499/10000000000 : ℝ), (142337459/500000000 : ℝ)] ![(40969965305013/100000000000000 : ℝ), (39986789918099/100000000000000 : ℝ), (297550699517/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2543216513/5000000000 : ℝ)|^33 ≤ (40969965305013/100000000000000 : ℝ)^25
        have hw : |(2543216513/5000000000 : ℝ)|=(2543216513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993690499/10000000000 : ℝ)|^33 ≤ (39986789918099/100000000000000 : ℝ)^25
        have hw : |(4993690499/10000000000 : ℝ)|=(4993690499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142337459/500000000 : ℝ)|^33 ≤ (297550699517/1562500000000 : ℝ)^25
        have hw : |(142337459/500000000 : ℝ)|=(142337459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2540520671/5000000000 : ℝ)*x 0 + (5002450401/10000000000 : ℝ)*x 1 + (-2842750513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2540520671/5000000000 : ℝ)^33 ≤ (20456324581731/50000000000000 : ℝ)^25 := by
    have hnat : (2540520671 : ℕ)^33*50000000000000^25 ≤ 20456324581731^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540520671 5000000000 20456324581731 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002450401/10000000000 : ℝ)^33 ≤ (40079406751063/100000000000000 : ℝ)^25 := by
    have hnat : (5002450401 : ℕ)^33*100000000000000^25 ≤ 40079406751063^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002450401 10000000000 40079406751063 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842750513/10000000000 : ℝ)^33 ≤ (3801588814613/20000000000000 : ℝ)^25 := by
    have hnat : (2842750513 : ℕ)^33*20000000000000^25 ≤ 3801588814613^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842750513 10000000000 3801588814613 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2540520671/5000000000 : ℝ), (5002450401/10000000000 : ℝ), (-2842750513/10000000000 : ℝ)] ![(20456324581731/50000000000000 : ℝ), (40079406751063/100000000000000 : ℝ), (3801588814613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2540520671/5000000000 : ℝ)|^33 ≤ (20456324581731/50000000000000 : ℝ)^25
        have hw : |(2540520671/5000000000 : ℝ)|=(2540520671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002450401/10000000000 : ℝ)|^33 ≤ (40079406751063/100000000000000 : ℝ)^25
        have hw : |(5002450401/10000000000 : ℝ)|=(5002450401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2842750513/10000000000 : ℝ)|^33 ≤ (3801588814613/20000000000000 : ℝ)^25
        have hw : |(-2842750513/10000000000 : ℝ)|=(2842750513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-997820619/5000000000 : ℝ)*x 0 + (4656763537/10000000000 : ℝ)*x 1 + (-6059517079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997820619/5000000000 : ℝ)^33 ≤ (148942580157/1250000000000 : ℝ)^25 := by
    have hnat : (997820619 : ℕ)^33*1250000000000^25 ≤ 148942580157^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997820619 5000000000 148942580157 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4656763537/10000000000 : ℝ)^33 ≤ (1458582895819/4000000000000 : ℝ)^25 := by
    have hnat : (4656763537 : ℕ)^33*4000000000000^25 ≤ 1458582895819^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656763537 10000000000 1458582895819 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6059517079/10000000000 : ℝ)^33 ≤ (51620021171859/100000000000000 : ℝ)^25 := by
    have hnat : (6059517079 : ℕ)^33*100000000000000^25 ≤ 51620021171859^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6059517079 10000000000 51620021171859 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-997820619/5000000000 : ℝ), (4656763537/10000000000 : ℝ), (-6059517079/10000000000 : ℝ)] ![(148942580157/1250000000000 : ℝ), (1458582895819/4000000000000 : ℝ), (51620021171859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-997820619/5000000000 : ℝ)|^33 ≤ (148942580157/1250000000000 : ℝ)^25
        have hw : |(-997820619/5000000000 : ℝ)|=(997820619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4656763537/10000000000 : ℝ)|^33 ≤ (1458582895819/4000000000000 : ℝ)^25
        have hw : |(4656763537/10000000000 : ℝ)|=(4656763537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6059517079/10000000000 : ℝ)|^33 ≤ (51620021171859/100000000000000 : ℝ)^25
        have hw : |(-6059517079/10000000000 : ℝ)|=(6059517079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (220392723/400000000 : ℝ)*x 0 + (-712702211/2500000000 : ℝ)*x 1 + (-4552477133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220392723/400000000 : ℝ)^33 ≤ (22765185148241/50000000000000 : ℝ)^25 := by
    have hnat : (220392723 : ℕ)^33*50000000000000^25 ≤ 22765185148241^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220392723 400000000 22765185148241 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712702211/2500000000 : ℝ)^33 ≤ (19079100189349/100000000000000 : ℝ)^25 := by
    have hnat : (712702211 : ℕ)^33*100000000000000^25 ≤ 19079100189349^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712702211 2500000000 19079100189349 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4552477133/10000000000 : ℝ)^33 ≤ (35390529495693/100000000000000 : ℝ)^25 := by
    have hnat : (4552477133 : ℕ)^33*100000000000000^25 ≤ 35390529495693^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552477133 10000000000 35390529495693 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220392723/400000000 : ℝ), (-712702211/2500000000 : ℝ), (-4552477133/10000000000 : ℝ)] ![(22765185148241/50000000000000 : ℝ), (19079100189349/100000000000000 : ℝ), (35390529495693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220392723/400000000 : ℝ)|^33 ≤ (22765185148241/50000000000000 : ℝ)^25
        have hw : |(220392723/400000000 : ℝ)|=(220392723/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-712702211/2500000000 : ℝ)|^33 ≤ (19079100189349/100000000000000 : ℝ)^25
        have hw : |(-712702211/2500000000 : ℝ)|=(712702211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4552477133/10000000000 : ℝ)|^33 ≤ (35390529495693/100000000000000 : ℝ)^25
        have hw : |(-4552477133/10000000000 : ℝ)|=(4552477133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5004328713/10000000000 : ℝ)*x 0 + (1000568841/2000000000 : ℝ)*x 1 + (293396919/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5004328713/10000000000 : ℝ)^33 ≤ (10024818139899/25000000000000 : ℝ)^25 := by
    have hnat : (5004328713 : ℕ)^33*25000000000000^25 ≤ 10024818139899^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004328713 10000000000 10024818139899 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000568841/2000000000 : ℝ)^33 ≤ (8016714317629/20000000000000 : ℝ)^25 := by
    have hnat : (1000568841 : ℕ)^33*20000000000000^25 ≤ 8016714317629^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000568841 2000000000 8016714317629 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293396919/1000000000 : ℝ)^33 ≤ (4954288959681/25000000000000 : ℝ)^25 := by
    have hnat : (293396919 : ℕ)^33*25000000000000^25 ≤ 4954288959681^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293396919 1000000000 4954288959681 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5004328713/10000000000 : ℝ), (1000568841/2000000000 : ℝ), (293396919/1000000000 : ℝ)] ![(10024818139899/25000000000000 : ℝ), (8016714317629/20000000000000 : ℝ), (4954288959681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5004328713/10000000000 : ℝ)|^33 ≤ (10024818139899/25000000000000 : ℝ)^25
        have hw : |(5004328713/10000000000 : ℝ)|=(5004328713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000568841/2000000000 : ℝ)|^33 ≤ (8016714317629/20000000000000 : ℝ)^25
        have hw : |(1000568841/2000000000 : ℝ)|=(1000568841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(293396919/1000000000 : ℝ)|^33 ≤ (4954288959681/25000000000000 : ℝ)^25
        have hw : |(293396919/1000000000 : ℝ)|=(293396919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s7_s7_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2511043279/5000000000 : ℝ)*x 0 + (2510419637/5000000000 : ℝ)*x 1 + (-1445716651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2511043279/5000000000 : ℝ)^33 ≤ (2517950296569/6250000000000 : ℝ)^25 := by
    have hnat : (2511043279 : ℕ)^33*6250000000000^25 ≤ 2517950296569^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511043279 5000000000 2517950296569 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510419637/5000000000 : ℝ)^33 ≤ (20136998860577/50000000000000 : ℝ)^25 := by
    have hnat : (2510419637 : ℕ)^33*50000000000000^25 ≤ 20136998860577^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510419637 5000000000 20136998860577 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1445716651/5000000000 : ℝ)^33 ≤ (9719398755833/50000000000000 : ℝ)^25 := by
    have hnat : (1445716651 : ℕ)^33*50000000000000^25 ≤ 9719398755833^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445716651 5000000000 9719398755833 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2511043279/5000000000 : ℝ), (2510419637/5000000000 : ℝ), (-1445716651/5000000000 : ℝ)] ![(2517950296569/6250000000000 : ℝ), (20136998860577/50000000000000 : ℝ), (9719398755833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2511043279/5000000000 : ℝ)|^33 ≤ (2517950296569/6250000000000 : ℝ)^25
        have hw : |(2511043279/5000000000 : ℝ)|=(2511043279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510419637/5000000000 : ℝ)|^33 ≤ (20136998860577/50000000000000 : ℝ)^25
        have hw : |(2510419637/5000000000 : ℝ)|=(2510419637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1445716651/5000000000 : ℝ)|^33 ≤ (9719398755833/50000000000000 : ℝ)^25
        have hw : |(-1445716651/5000000000 : ℝ)|=(1445716651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302054_s7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev6 : (0 : ℝ) ≤ ((19983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10483/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6661/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6661/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15511/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15511/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8239/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8239/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2109/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2109/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (19983/100000 : ℝ) ^ (65/16 : ℝ) ≤ (144189636350085761/100000000000000000000 : ℝ) := by
    have hpowers : (19983/100000 : ℝ)^65 ≤ (144189636350085761/100000000000000000000 : ℝ)^16 := by
      have hnat : (19983 : ℕ)^65*100000000000000000000^16 ≤ 144189636350085761^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19983 100000 144189636350085761 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19983/100000 : ℝ)) (X := (144189636350085761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner0a : (100144189636350085761/100000000000000000000 : ℝ) ≤ (400141894240079/400000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100144189636350085761/100000000000000000000 : ℝ)^16 ≤ (400141894240079/400000000000000 : ℝ)^65 := by
      have hnat : (100144189636350085761 : ℕ)^16*400000000000000^65 ≤ 400141894240079^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100144189636350085761 100000000000000000000 400141894240079 400000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400141894240079/400000000000000 : ℝ)) (X := (100144189636350085761/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner0b : (50144189636350085761/50000000000000000000 : ℝ) ≤ (2501772715945031/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50144189636350085761/50000000000000000000 : ℝ)^16 ≤ (2501772715945031/2500000000000000 : ℝ)^65 := by
      have hnat : (50144189636350085761 : ℕ)^16*2500000000000000^65 ≤ 2501772715945031^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50144189636350085761 50000000000000000000 2501772715945031 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501772715945031/2500000000000000 : ℝ)) (X := (50144189636350085761/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141894240079/79932000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1181169259383/666100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (19983/100000 : ℝ)) (alpha := (141894240079/79932000000000 : ℝ)) (beta := (1181169259383/666100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (19983/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141894240079/79932000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1181169259383/666100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (10483/50000 : ℝ) ^ (65/16 : ℝ) ≤ (10953100360724721/6250000000000000000 : ℝ) := by
    have hpowers : (10483/50000 : ℝ)^65 ≤ (10953100360724721/6250000000000000000 : ℝ)^16 := by
      have hnat : (10483 : ℕ)^65*6250000000000000000^16 ≤ 10953100360724721^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10483 50000 10953100360724721 6250000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10483/50000 : ℝ)) (X := (10953100360724721/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner1a : (6260953100360724721/6250000000000000000 : ℝ) ≤ (10004310989834253/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (6260953100360724721/6250000000000000000 : ℝ)^16 ≤ (10004310989834253/10000000000000000 : ℝ)^65 := by
      have hnat : (6260953100360724721 : ℕ)^16*10000000000000000^65 ≤ 10004310989834253^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6260953100360724721 6250000000000000000 10004310989834253 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004310989834253/10000000000000000 : ℝ)) (X := (6260953100360724721/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner1b : (3135953100360724721/3125000000000000000 : ℝ) ≤ (5004308149036569/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3135953100360724721/3125000000000000000 : ℝ)^16 ≤ (5004308149036569/5000000000000000 : ℝ)^65 := by
      have hnat : (3135953100360724721 : ℕ)^16*5000000000000000^65 ≤ 5004308149036569^65*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3135953100360724721 3125000000000000000 5004308149036569 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004308149036569/5000000000000000 : ℝ)) (X := (3135953100360724721/3125000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(4310989834253/2096600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(861061647777/419320000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (10483/50000 : ℝ)) (alpha := (4310989834253/2096600000000000 : ℝ)) (beta := (861061647777/419320000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10483/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(4310989834253/2096600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(861061647777/419320000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (6661/50000 : ℝ) ^ (65/16 : ℝ) ≤ (27769196050373231/100000000000000000000 : ℝ) := by
    have hpowers : (6661/50000 : ℝ)^65 ≤ (27769196050373231/100000000000000000000 : ℝ)^16 := by
      have hnat : (6661 : ℕ)^65*100000000000000000000^16 ≤ 27769196050373231^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6661 50000 27769196050373231 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6661/50000 : ℝ)) (X := (27769196050373231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner2a : (100027769196050373231/100000000000000000000 : ℝ) ≤ (10000683477906753/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100027769196050373231/100000000000000000000 : ℝ)^16 ≤ (10000683477906753/10000000000000000 : ℝ)^65 := by
      have hnat : (100027769196050373231 : ℕ)^16*10000000000000000^65 ≤ 10000683477906753^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027769196050373231 100000000000000000000 10000683477906753 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683477906753/10000000000000000 : ℝ)) (X := (100027769196050373231/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner2b : (50027769196050373231/50000000000000000000 : ℝ) ≤ (2500341703197741/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50027769196050373231/50000000000000000000 : ℝ)^16 ≤ (2500341703197741/2500000000000000 : ℝ)^65 := by
      have hnat : (50027769196050373231 : ℕ)^16*2500000000000000^65 ≤ 2500341703197741^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027769196050373231 50000000000000000000 2500341703197741 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500341703197741/2500000000000000 : ℝ)) (X := (50027769196050373231/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(683477906753/1332200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(683334884211/1332200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (6661/50000 : ℝ)) (alpha := (683477906753/1332200000000000 : ℝ)) (beta := (683334884211/1332200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6661/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(683477906753/1332200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(683334884211/1332200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-130525913/625000000 : ℝ)*X 0 0+(1145720869/2500000000 : ℝ)*X 0 1+(-378859497/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((5416790761/10000000000 : ℝ)*X 1 0+(-73110879/250000000 : ℝ)*X 1 1+(-573425907/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((1002225367/2000000000 : ℝ)*X 2 0+(2504822893/5000000000 : ℝ)*X 2 1+(1458909247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((5008266839/10000000000 : ℝ)*X 0 0+(625876607/1250000000 : ℝ)*X 0 1+(-2924346059/10000000000 : ℝ)*X 0 2+(5008266839/10000000000 : ℝ)*X 1 0+(625876607/1250000000 : ℝ)*X 1 1+(-2924346059/10000000000 : ℝ)*X 1 2+(5008266839/10000000000 : ℝ)*X 2 0+(625876607/1250000000 : ℝ)*X 2 1+(-2924346059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-2081648217/10000000000 : ℝ)*X 0 0+(4538645393/10000000000 : ℝ)*X 0 1+(-3053447749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((5406416511/10000000000 : ℝ)*X 1 0+(-357097803/1250000000 : ℝ)*X 1 1+(-582067049/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((998907731/2000000000 : ℝ)*X 2 0+(5083767137/10000000000 : ℝ)*X 2 1+(2848943329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((5007003837/10000000000 : ℝ)*X 0 0+(5082764807/10000000000 : ℝ)*X 0 1+(-708803719/2500000000 : ℝ)*X 0 2+(5007003837/10000000000 : ℝ)*X 1 0+(5082764807/10000000000 : ℝ)*X 1 1+(-708803719/2500000000 : ℝ)*X 1 2+(5007003837/10000000000 : ℝ)*X 2 0+(5082764807/10000000000 : ℝ)*X 2 1+(-708803719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-2029590249/10000000000 : ℝ)*X 0 0+(286447213/625000000 : ℝ)*X 0 1+(-6103096527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((5364038887/10000000000 : ℝ)*X 1 0+(-181624391/625000000 : ℝ)*X 1 1+(-4658730729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((2543216513/5000000000 : ℝ)*X 2 0+(4993690499/10000000000 : ℝ)*X 2 1+(142337459/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((2540520671/5000000000 : ℝ)*X 0 0+(5002450401/10000000000 : ℝ)*X 0 1+(-2842750513/10000000000 : ℝ)*X 0 2+(2540520671/5000000000 : ℝ)*X 1 0+(5002450401/10000000000 : ℝ)*X 1 1+(-2842750513/10000000000 : ℝ)*X 1 2+(2540520671/5000000000 : ℝ)*X 2 0+(5002450401/10000000000 : ℝ)*X 2 1+(-2842750513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-997820619/5000000000 : ℝ)*X 0 0+(4656763537/10000000000 : ℝ)*X 0 1+(-6059517079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((220392723/400000000 : ℝ)*X 1 0+(-712702211/2500000000 : ℝ)*X 1 1+(-4552477133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((5004328713/10000000000 : ℝ)*X 2 0+(1000568841/2000000000 : ℝ)*X 2 1+(293396919/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((2511043279/5000000000 : ℝ)*X 0 0+(2510419637/5000000000 : ℝ)*X 0 1+(-1445716651/5000000000 : ℝ)*X 0 2+(2511043279/5000000000 : ℝ)*X 1 0+(2510419637/5000000000 : ℝ)*X 1 1+(-1445716651/5000000000 : ℝ)*X 1 2+(2511043279/5000000000 : ℝ)*X 2 0+(2510419637/5000000000 : ℝ)*X 2 1+(-1445716651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((15511/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15511/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12233972488197685509387621/3491363150000000000000000000000 : ℝ) := by norm_num
    linear_combination (1584555032591/125000000000 : ℝ)*(base39) + (47203429019/12500000000 : ℝ)*(base60) + (16766334846693/250000000000 : ℝ)*(major_s7_0) + (16766334846693/250000000000 : ℝ)*(major_s7_1) + (16766334846693/250000000000 : ℝ)*(major_s7_2) + (781003357/250000000000 : ℝ)*(sp_s7_0) + (1780560407/1000000000000 : ℝ)*(sp_s7_6) + (89168464225877/1000000000000 : ℝ)*(sp_s7_7) + (22292884211271/250000000000 : ℝ)*(sp_s7_8) + (89171638103979/1000000000000 : ℝ)*(sp_s7_9) + (44957218827387/1000000000000 : ℝ)*(sp_s7_13) + (89978419/1000000000000 : ℝ)*(sp_s7_14) + (883579/6250000000 : ℝ)*(sp_s7_15) + (8022749/200000000000 : ℝ)*(sp_s7_23) + (22479499693897/500000000000 : ℝ)*(f.failure) + (22292919554431/250000000000 : ℝ)*(f.sum) + (3168033955437139/872840787500000000000000000000 : ℝ)*base63 + (118721025994587/333050000000000000000000000 : ℝ)*base64 + (40076583364859/104830000000000000000000000 : ℝ)*base67 + (128987280553951/333050000000000000000000000 : ℝ)*base68 + (3804411376737/83262500000000000000000000 : ℝ)*base71 + (275888045656303/333050000000000000000000000 : ℝ)*base73 + (191960881834801/524150000000000000000000000 : ℝ)*base74 + (23829786511399/66610000000000000000000000 : ℝ)*base76 + (1500118790929221109/3491363150000000000000000000000 : ℝ)*base79 + (1549/5000000000000000 : ℝ)*base87 + (1549/5000000000000000 : ℝ)*base89 + (1549/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8239/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8239/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15750672399577933633832151/1745681575000000000000000000000 : ℝ) := by norm_num
    linear_combination (6330205440341/500000000000 : ℝ)*(base39) + (896673993563/250000000000 : ℝ)*(base60) + (67264959456507/1000000000000 : ℝ)*(major_s7_0) + (67264959456507/1000000000000 : ℝ)*(major_s7_1) + (67264959456507/1000000000000 : ℝ)*(major_s7_2) + (136338827/5000000000 : ℝ)*(sp_s7_0) + (20979123/976562500 : ℝ)*(sp_s7_6) + (3180126431/200000000000 : ℝ)*(sp_s7_8) + (89395346556101/1000000000000 : ℝ)*(sp_s7_14) + (3576847814619/40000000000 : ℝ)*(sp_s7_15) + (11179585994169/125000000000 : ℝ)*(sp_s7_16) + (11267834321469/250000000000 : ℝ)*(sp_s7_20) + (14481676129/1000000000000 : ℝ)*(sp_s7_21) + (204022139/500000000000 : ℝ)*(sp_s7_23) + (11273204976957/250000000000 : ℝ)*(f.failure) + (89437095997631/1000000000000 : ℝ)*(f.sum) + (80506606581644987/436420393750000000000000000000 : ℝ)*base63 + (195337407161203/1332200000000000000000000000 : ℝ)*base64 + (62399681839571/419320000000000000000000000 : ℝ)*base66 + (452797712014771/1332200000000000000000000000 : ℝ)*base69 + (396205106956433/1332200000000000000000000000 : ℝ)*base70 + (358809066208309/666100000000000000000000000 : ℝ)*base72 + (233513223787511/2096600000000000000000000000 : ℝ)*base75 + (13703137138783/133220000000000000000000000 : ℝ)*base77 + (5330073815026900789/13965452600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (69/2500000000000000 : ℝ)*base87 + (69/2500000000000000 : ℝ)*base89 + (69/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2109/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2109/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4170671685724974372208187/698272630000000000000000000000 : ℝ) := by norm_num
    linear_combination (8189452920003/1000000000000 : ℝ)*(base39) + (4900157/1000000000000 : ℝ)*(base50) + (233083785683/125000000000 : ℝ)*(base60) + (20832685558741/500000000000 : ℝ)*(major_s7_0) + (20832685558741/500000000000 : ℝ)*(major_s7_1) + (20832685558741/500000000000 : ℝ)*(major_s7_2) + (3837423/10000000000 : ℝ)*(sp_s7_1) + (100308577/100000000000 : ℝ)*(sp_s7_2) + (162487169/500000000000 : ℝ)*(sp_s7_13) + (934456363/1000000000000 : ℝ)*(sp_s7_20) + (1731227251301/31250000000 : ℝ)*(sp_s7_21) + (13849722074833/250000000000 : ℝ)*(sp_s7_22) + (27699134477931/500000000000 : ℝ)*(sp_s7_23) + (3491276096459/125000000000 : ℝ)*(sp_s7_27) + (13965734101187/500000000000 : ℝ)*(f.failure) + (1731227251301/31250000000 : ℝ)*(f.sum) + (1928029366294201763/1745681575000000000000000000000 : ℝ)*base63 + (341836023799341/666100000000000000000000000 : ℝ)*base65 + (149717952995843/209660000000000000000000000 : ℝ)*base66 + (976503921940893/666100000000000000000000000 : ℝ)*base69 + (271106424284333/1998300000000000000000000000 : ℝ)*base71 + (38434311592031/166525000000000000000000000 : ℝ)*base72 + (1067255987074753/1048300000000000000000000000 : ℝ)*base75 + (99569142737137/99915000000000000000000000 : ℝ)*base77 + (1122330287965499143/6982726300000000000000000000000 : ℝ)*base79 + (3521/5000000000000000 : ℝ)*base86 + (3521/5000000000000000 : ℝ)*base88 + (3521/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev6 : (0 : ℝ) ≤ ((19983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10483/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6661/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6661/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15511/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15511/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8239/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8239/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2109/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2109/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302054_s7 p hpa hpb X hX hprev6

#print axioms solution
