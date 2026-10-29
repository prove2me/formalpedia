-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308063_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:39:34.528977+00:00
-- url     : https://prove2.me/submissions/7317132e-f2de-45b7-b7b7-29c6e438b568

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
theorem collision_support_c308063_s4_s4_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-644349453/5000000000 : ℝ)*x 0 + (220587991/400000000 : ℝ)*x 1 + (13993603/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (644349453/5000000000 : ℝ)^69 ≤ (277701310739/4000000000000 : ℝ)^53 := by
    have hnat : (644349453 : ℕ)^69*4000000000000^53 ≤ 277701310739^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644349453 5000000000 277701310739 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220587991/400000000 : ℝ)^69 ≤ (23038847286253/50000000000000 : ℝ)^53 := by
    have hnat : (220587991 : ℕ)^69*50000000000000^53 ≤ 23038847286253^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220587991 400000000 23038847286253 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13993603/25000000 : ℝ)^69 ≤ (46979772643077/100000000000000 : ℝ)^53 := by
    have hnat : (13993603 : ℕ)^69*100000000000000^53 ≤ 46979772643077^53*25000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13993603 25000000 46979772643077 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-644349453/5000000000 : ℝ), (220587991/400000000 : ℝ), (13993603/25000000 : ℝ)] ![(277701310739/4000000000000 : ℝ), (23038847286253/50000000000000 : ℝ), (46979772643077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-644349453/5000000000 : ℝ)|^69 ≤ (277701310739/4000000000000 : ℝ)^53
        have hw : |(-644349453/5000000000 : ℝ)|=(644349453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220587991/400000000 : ℝ)|^69 ≤ (23038847286253/50000000000000 : ℝ)^53
        have hw : |(220587991/400000000 : ℝ)|=(220587991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13993603/25000000 : ℝ)|^69 ≤ (46979772643077/100000000000000 : ℝ)^53
        have hw : |(13993603/25000000 : ℝ)|=(13993603/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1103164573/2000000000 : ℝ)*x 0 + (-260393457/2000000000 : ℝ)*x 1 + (5587790861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103164573/2000000000 : ℝ)^69 ≤ (46089911725107/100000000000000 : ℝ)^53 := by
    have hnat : (1103164573 : ℕ)^69*100000000000000^53 ≤ 46089911725107^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103164573 2000000000 46089911725107 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260393457/2000000000 : ℝ)^69 ≤ (7035735872407/100000000000000 : ℝ)^53 := by
    have hnat : (260393457 : ℕ)^69*100000000000000^53 ≤ 7035735872407^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260393457 2000000000 7035735872407 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5587790861/10000000000 : ℝ)^69 ≤ (46874352383251/100000000000000 : ℝ)^53 := by
    have hnat : (5587790861 : ℕ)^69*100000000000000^53 ≤ 46874352383251^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587790861 10000000000 46874352383251 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103164573/2000000000 : ℝ), (-260393457/2000000000 : ℝ), (5587790861/10000000000 : ℝ)] ![(46089911725107/100000000000000 : ℝ), (7035735872407/100000000000000 : ℝ), (46874352383251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103164573/2000000000 : ℝ)|^69 ≤ (46089911725107/100000000000000 : ℝ)^53
        have hw : |(1103164573/2000000000 : ℝ)|=(1103164573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260393457/2000000000 : ℝ)|^69 ≤ (7035735872407/100000000000000 : ℝ)^53
        have hw : |(-260393457/2000000000 : ℝ)|=(260393457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5587790861/10000000000 : ℝ)|^69 ≤ (46874352383251/100000000000000 : ℝ)^53
        have hw : |(5587790861/10000000000 : ℝ)|=(5587790861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (277996873/500000000 : ℝ)*x 0 + (1114962683/2000000000 : ℝ)*x 1 + (-313383963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277996873/500000000 : ℝ)^69 ≤ (46570390363617/100000000000000 : ℝ)^53 := by
    have hnat : (277996873 : ℕ)^69*100000000000000^53 ≤ 46570390363617^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277996873 500000000 46570390363617 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114962683/2000000000 : ℝ)^69 ≤ (46732673464619/100000000000000 : ℝ)^53 := by
    have hnat : (1114962683 : ℕ)^69*100000000000000^53 ≤ 46732673464619^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114962683 2000000000 46732673464619 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313383963/2500000000 : ℝ)^69 ≤ (267877446259/4000000000000 : ℝ)^53 := by
    have hnat : (313383963 : ℕ)^69*4000000000000^53 ≤ 267877446259^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313383963 2500000000 267877446259 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277996873/500000000 : ℝ), (1114962683/2000000000 : ℝ), (-313383963/2500000000 : ℝ)] ![(46570390363617/100000000000000 : ℝ), (46732673464619/100000000000000 : ℝ), (267877446259/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277996873/500000000 : ℝ)|^69 ≤ (46570390363617/100000000000000 : ℝ)^53
        have hw : |(277996873/500000000 : ℝ)|=(277996873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1114962683/2000000000 : ℝ)|^69 ≤ (46732673464619/100000000000000 : ℝ)^53
        have hw : |(1114962683/2000000000 : ℝ)|=(1114962683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-313383963/2500000000 : ℝ)|^69 ≤ (267877446259/4000000000000 : ℝ)^53
        have hw : |(-313383963/2500000000 : ℝ)|=(313383963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4374004573/10000000000 : ℝ)*x 0 + (4315040339/10000000000 : ℝ)*x 1 + (4211880979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374004573/10000000000 : ℝ)^69 ≤ (17038659362131/50000000000000 : ℝ)^53 := by
    have hnat : (4374004573 : ℕ)^69*50000000000000^53 ≤ 17038659362131^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374004573 10000000000 17038659362131 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4315040339/10000000000 : ℝ)^69 ≤ (6696094990741/20000000000000 : ℝ)^53 := by
    have hnat : (4315040339 : ℕ)^69*20000000000000^53 ≤ 6696094990741^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315040339 10000000000 6696094990741 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4211880979/10000000000 : ℝ)^69 ≤ (16221103148591/50000000000000 : ℝ)^53 := by
    have hnat : (4211880979 : ℕ)^69*50000000000000^53 ≤ 16221103148591^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211880979 10000000000 16221103148591 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374004573/10000000000 : ℝ), (4315040339/10000000000 : ℝ), (4211880979/10000000000 : ℝ)] ![(17038659362131/50000000000000 : ℝ), (6696094990741/20000000000000 : ℝ), (16221103148591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374004573/10000000000 : ℝ)|^69 ≤ (17038659362131/50000000000000 : ℝ)^53
        have hw : |(4374004573/10000000000 : ℝ)|=(4374004573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4315040339/10000000000 : ℝ)|^69 ≤ (6696094990741/20000000000000 : ℝ)^53
        have hw : |(4315040339/10000000000 : ℝ)|=(4315040339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4211880979/10000000000 : ℝ)|^69 ≤ (16221103148591/50000000000000 : ℝ)^53
        have hw : |(4211880979/10000000000 : ℝ)|=(4211880979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-507607229/5000000000 : ℝ)*x 0 + (4447779193/10000000000 : ℝ)*x 1 + (6761719807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507607229/5000000000 : ℝ)^69 ≤ (2544606998857/50000000000000 : ℝ)^53 := by
    have hnat : (507607229 : ℕ)^69*50000000000000^53 ≤ 2544606998857^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507607229 5000000000 2544606998857 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4447779193/10000000000 : ℝ)^69 ≤ (3482750023199/10000000000000 : ℝ)^53 := by
    have hnat : (4447779193 : ℕ)^69*10000000000000^53 ≤ 3482750023199^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447779193 10000000000 3482750023199 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6761719807/10000000000 : ℝ)^69 ≤ (15020821437879/25000000000000 : ℝ)^53 := by
    have hnat : (6761719807 : ℕ)^69*25000000000000^53 ≤ 15020821437879^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6761719807 10000000000 15020821437879 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507607229/5000000000 : ℝ), (4447779193/10000000000 : ℝ), (6761719807/10000000000 : ℝ)] ![(2544606998857/50000000000000 : ℝ), (3482750023199/10000000000000 : ℝ), (15020821437879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507607229/5000000000 : ℝ)|^69 ≤ (2544606998857/50000000000000 : ℝ)^53
        have hw : |(-507607229/5000000000 : ℝ)|=(507607229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4447779193/10000000000 : ℝ)|^69 ≤ (3482750023199/10000000000000 : ℝ)^53
        have hw : |(4447779193/10000000000 : ℝ)|=(4447779193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6761719807/10000000000 : ℝ)|^69 ≤ (15020821437879/25000000000000 : ℝ)^53
        have hw : |(6761719807/10000000000 : ℝ)|=(6761719807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (24209403/50000000 : ℝ)*x 0 + (-64041513/2000000000 : ℝ)*x 1 + (6751861341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24209403/50000000 : ℝ)^69 ≤ (38897705618921/100000000000000 : ℝ)^53 := by
    have hnat : (24209403 : ℕ)^69*100000000000000^53 ≤ 38897705618921^53*50000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24209403 50000000 38897705618921 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64041513/2000000000 : ℝ)^69 ≤ (226605851257/20000000000000 : ℝ)^53 := by
    have hnat : (64041513 : ℕ)^69*20000000000000^53 ≤ 226605851257^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64041513 2000000000 226605851257 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6751861341/10000000000 : ℝ)^69 ≤ (59969265118167/100000000000000 : ℝ)^53 := by
    have hnat : (6751861341 : ℕ)^69*100000000000000^53 ≤ 59969265118167^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6751861341 10000000000 59969265118167 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24209403/50000000 : ℝ), (-64041513/2000000000 : ℝ), (6751861341/10000000000 : ℝ)] ![(38897705618921/100000000000000 : ℝ), (226605851257/20000000000000 : ℝ), (59969265118167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24209403/50000000 : ℝ)|^69 ≤ (38897705618921/100000000000000 : ℝ)^53
        have hw : |(24209403/50000000 : ℝ)|=(24209403/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64041513/2000000000 : ℝ)|^69 ≤ (226605851257/20000000000000 : ℝ)^53
        have hw : |(-64041513/2000000000 : ℝ)|=(64041513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6751861341/10000000000 : ℝ)|^69 ≤ (59969265118167/100000000000000 : ℝ)^53
        have hw : |(6751861341/10000000000 : ℝ)|=(6751861341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (571100643/1250000000 : ℝ)*x 0 + (3512905713/5000000000 : ℝ)*x 1 + (-119887241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (571100643/1250000000 : ℝ)^69 ≤ (36066296205813/100000000000000 : ℝ)^53 := by
    have hnat : (571100643 : ℕ)^69*100000000000000^53 ≤ 36066296205813^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571100643 1250000000 36066296205813 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3512905713/5000000000 : ℝ)^69 ≤ (31578113998209/50000000000000 : ℝ)^53 := by
    have hnat : (3512905713 : ℕ)^69*50000000000000^53 ≤ 31578113998209^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3512905713 5000000000 31578113998209 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119887241/5000000000 : ℝ)^69 ≤ (388737895003/50000000000000 : ℝ)^53 := by
    have hnat : (119887241 : ℕ)^69*50000000000000^53 ≤ 388737895003^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119887241 5000000000 388737895003 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(571100643/1250000000 : ℝ), (3512905713/5000000000 : ℝ), (-119887241/5000000000 : ℝ)] ![(36066296205813/100000000000000 : ℝ), (31578113998209/50000000000000 : ℝ), (388737895003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(571100643/1250000000 : ℝ)|^69 ≤ (36066296205813/100000000000000 : ℝ)^53
        have hw : |(571100643/1250000000 : ℝ)|=(571100643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3512905713/5000000000 : ℝ)|^69 ≤ (31578113998209/50000000000000 : ℝ)^53
        have hw : |(3512905713/5000000000 : ℝ)|=(3512905713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-119887241/5000000000 : ℝ)|^69 ≤ (388737895003/50000000000000 : ℝ)^53
        have hw : |(-119887241/5000000000 : ℝ)|=(119887241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1102229199/2500000000 : ℝ)*x 0 + (6171633071/10000000000 : ℝ)*x 1 + (198951399/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102229199/2500000000 : ℝ)^69 ≤ (17215926757861/50000000000000 : ℝ)^53 := by
    have hnat : (1102229199 : ℕ)^69*50000000000000^53 ≤ 17215926757861^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102229199 2500000000 17215926757861 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6171633071/10000000000 : ℝ)^69 ≤ (26674400014793/50000000000000 : ℝ)^53 := by
    have hnat : (6171633071 : ℕ)^69*50000000000000^53 ≤ 26674400014793^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6171633071 10000000000 26674400014793 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198951399/1000000000 : ℝ)^69 ≤ (6109673216431/50000000000000 : ℝ)^53 := by
    have hnat : (198951399 : ℕ)^69*50000000000000^53 ≤ 6109673216431^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198951399 1000000000 6109673216431 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102229199/2500000000 : ℝ), (6171633071/10000000000 : ℝ), (198951399/1000000000 : ℝ)] ![(17215926757861/50000000000000 : ℝ), (26674400014793/50000000000000 : ℝ), (6109673216431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102229199/2500000000 : ℝ)|^69 ≤ (17215926757861/50000000000000 : ℝ)^53
        have hw : |(1102229199/2500000000 : ℝ)|=(1102229199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6171633071/10000000000 : ℝ)|^69 ≤ (26674400014793/50000000000000 : ℝ)^53
        have hw : |(6171633071/10000000000 : ℝ)|=(6171633071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198951399/1000000000 : ℝ)|^69 ≤ (6109673216431/50000000000000 : ℝ)^53
        have hw : |(198951399/1000000000 : ℝ)|=(198951399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-292798057/10000000000 : ℝ)*x 0 + (2429367413/5000000000 : ℝ)*x 1 + (6747383943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (292798057/10000000000 : ℝ)^69 ≤ (1008429124323/100000000000000 : ℝ)^53 := by
    have hnat : (292798057 : ℕ)^69*100000000000000^53 ≤ 1008429124323^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292798057 10000000000 1008429124323 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2429367413/5000000000 : ℝ)^69 ≤ (39074073658557/100000000000000 : ℝ)^53 := by
    have hnat : (2429367413 : ℕ)^69*100000000000000^53 ≤ 39074073658557^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429367413 5000000000 39074073658557 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6747383943/10000000000 : ℝ)^69 ≤ (11983499441101/20000000000000 : ℝ)^53 := by
    have hnat : (6747383943 : ℕ)^69*20000000000000^53 ≤ 11983499441101^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6747383943 10000000000 11983499441101 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-292798057/10000000000 : ℝ), (2429367413/5000000000 : ℝ), (6747383943/10000000000 : ℝ)] ![(1008429124323/100000000000000 : ℝ), (39074073658557/100000000000000 : ℝ), (11983499441101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-292798057/10000000000 : ℝ)|^69 ≤ (1008429124323/100000000000000 : ℝ)^53
        have hw : |(-292798057/10000000000 : ℝ)|=(292798057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2429367413/5000000000 : ℝ)|^69 ≤ (39074073658557/100000000000000 : ℝ)^53
        have hw : |(2429367413/5000000000 : ℝ)|=(2429367413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6747383943/10000000000 : ℝ)|^69 ≤ (11983499441101/20000000000000 : ℝ)^53
        have hw : |(6747383943/10000000000 : ℝ)|=(6747383943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4483290887/10000000000 : ℝ)*x 0 + (-62656913/625000000 : ℝ)*x 1 + (1684382233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483290887/10000000000 : ℝ)^69 ≤ (3518994831253/10000000000000 : ℝ)^53 := by
    have hnat : (4483290887 : ℕ)^69*10000000000000^53 ≤ 3518994831253^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483290887 10000000000 3518994831253 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62656913/625000000 : ℝ)^69 ≤ (200258483639/4000000000000 : ℝ)^53 := by
    have hnat : (62656913 : ℕ)^69*4000000000000^53 ≤ 200258483639^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62656913 625000000 200258483639 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684382233/2500000000 : ℝ)^69 ≤ (59803589583213/100000000000000 : ℝ)^53 := by
    have hnat : (1684382233 : ℕ)^69*100000000000000^53 ≤ 59803589583213^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684382233 2500000000 59803589583213 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483290887/10000000000 : ℝ), (-62656913/625000000 : ℝ), (1684382233/2500000000 : ℝ)] ![(3518994831253/10000000000000 : ℝ), (200258483639/4000000000000 : ℝ), (59803589583213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483290887/10000000000 : ℝ)|^69 ≤ (3518994831253/10000000000000 : ℝ)^53
        have hw : |(4483290887/10000000000 : ℝ)|=(4483290887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62656913/625000000 : ℝ)|^69 ≤ (200258483639/4000000000000 : ℝ)^53
        have hw : |(-62656913/625000000 : ℝ)|=(62656913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1684382233/2500000000 : ℝ)|^69 ≤ (59803589583213/100000000000000 : ℝ)^53
        have hw : |(1684382233/2500000000 : ℝ)|=(1684382233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (838286261/1250000000 : ℝ)*x 0 + (4920180741/10000000000 : ℝ)*x 1 + (-254108039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838286261/1250000000 : ℝ)^69 ≤ (74303566023/125000000000 : ℝ)^53 := by
    have hnat : (838286261 : ℕ)^69*125000000000^53 ≤ 74303566023^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838286261 1250000000 74303566023 125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4920180741/10000000000 : ℝ)^69 ≤ (39718625041019/100000000000000 : ℝ)^53 := by
    have hnat : (4920180741 : ℕ)^69*100000000000000^53 ≤ 39718625041019^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4920180741 10000000000 39718625041019 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254108039/10000000000 : ℝ)^69 ≤ (209630531529/25000000000000 : ℝ)^53 := by
    have hnat : (254108039 : ℕ)^69*25000000000000^53 ≤ 209630531529^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254108039 10000000000 209630531529 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838286261/1250000000 : ℝ), (4920180741/10000000000 : ℝ), (-254108039/10000000000 : ℝ)] ![(74303566023/125000000000 : ℝ), (39718625041019/100000000000000 : ℝ), (209630531529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838286261/1250000000 : ℝ)|^69 ≤ (74303566023/125000000000 : ℝ)^53
        have hw : |(838286261/1250000000 : ℝ)|=(838286261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4920180741/10000000000 : ℝ)|^69 ≤ (39718625041019/100000000000000 : ℝ)^53
        have hw : |(4920180741/10000000000 : ℝ)|=(4920180741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254108039/10000000000 : ℝ)|^69 ≤ (209630531529/25000000000000 : ℝ)^53
        have hw : |(-254108039/10000000000 : ℝ)|=(254108039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3418138327/5000000000 : ℝ)*x 0 + (225930627/625000000 : ℝ)*x 1 + (1010053277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3418138327/5000000000 : ℝ)^69 ≤ (30473606958359/50000000000000 : ℝ)^53 := by
    have hnat : (3418138327 : ℕ)^69*50000000000000^53 ≤ 30473606958359^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3418138327 5000000000 30473606958359 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225930627/625000000 : ℝ)^69 ≤ (26588254947141/100000000000000 : ℝ)^53 := by
    have hnat : (225930627 : ℕ)^69*100000000000000^53 ≤ 26588254947141^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225930627 625000000 26588254947141 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010053277/5000000000 : ℝ)^69 ≤ (623226556227/5000000000000 : ℝ)^53 := by
    have hnat : (1010053277 : ℕ)^69*5000000000000^53 ≤ 623226556227^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010053277 5000000000 623226556227 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3418138327/5000000000 : ℝ), (225930627/625000000 : ℝ), (1010053277/5000000000 : ℝ)] ![(30473606958359/50000000000000 : ℝ), (26588254947141/100000000000000 : ℝ), (623226556227/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3418138327/5000000000 : ℝ)|^69 ≤ (30473606958359/50000000000000 : ℝ)^53
        have hw : |(3418138327/5000000000 : ℝ)|=(3418138327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225930627/625000000 : ℝ)|^69 ≤ (26588254947141/100000000000000 : ℝ)^53
        have hw : |(225930627/625000000 : ℝ)|=(225930627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010053277/5000000000 : ℝ)|^69 ≤ (623226556227/5000000000000 : ℝ)^53
        have hw : |(1010053277/5000000000 : ℝ)|=(1010053277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-240426483/10000000000 : ℝ)*x 0 + (394367663/625000000 : ℝ)*x 1 + (5351452541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240426483/10000000000 : ℝ)^69 ≤ (780229279999/100000000000000 : ℝ)^53 := by
    have hnat : (240426483 : ℕ)^69*100000000000000^53 ≤ 780229279999^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240426483 10000000000 780229279999 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394367663/625000000 : ℝ)^69 ≤ (54909861086457/100000000000000 : ℝ)^53 := by
    have hnat : (394367663 : ℕ)^69*100000000000000^53 ≤ 54909861086457^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394367663 625000000 54909861086457 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5351452541/10000000000 : ℝ)^69 ≤ (44309909616813/100000000000000 : ℝ)^53 := by
    have hnat : (5351452541 : ℕ)^69*100000000000000^53 ≤ 44309909616813^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351452541 10000000000 44309909616813 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240426483/10000000000 : ℝ), (394367663/625000000 : ℝ), (5351452541/10000000000 : ℝ)] ![(780229279999/100000000000000 : ℝ), (54909861086457/100000000000000 : ℝ), (44309909616813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240426483/10000000000 : ℝ)|^69 ≤ (780229279999/100000000000000 : ℝ)^53
        have hw : |(-240426483/10000000000 : ℝ)|=(240426483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(394367663/625000000 : ℝ)|^69 ≤ (54909861086457/100000000000000 : ℝ)^53
        have hw : |(394367663/625000000 : ℝ)|=(394367663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5351452541/10000000000 : ℝ)|^69 ≤ (44309909616813/100000000000000 : ℝ)^53
        have hw : |(5351452541/10000000000 : ℝ)|=(5351452541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (671358331/1000000000 : ℝ)*x 0 + (-234880547/10000000000 : ℝ)*x 1 + (196797589/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671358331/1000000000 : ℝ)^69 ≤ (14881756862801/25000000000000 : ℝ)^53 := by
    have hnat : (671358331 : ℕ)^69*25000000000000^53 ≤ 14881756862801^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671358331 1000000000 14881756862801 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234880547/10000000000 : ℝ)^69 ≤ (378440227927/50000000000000 : ℝ)^53 := by
    have hnat : (234880547 : ℕ)^69*50000000000000^53 ≤ 378440227927^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234880547 10000000000 378440227927 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196797589/400000000 : ℝ)^69 ≤ (9929023019231/25000000000000 : ℝ)^53 := by
    have hnat : (196797589 : ℕ)^69*25000000000000^53 ≤ 9929023019231^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196797589 400000000 9929023019231 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671358331/1000000000 : ℝ), (-234880547/10000000000 : ℝ), (196797589/400000000 : ℝ)] ![(14881756862801/25000000000000 : ℝ), (378440227927/50000000000000 : ℝ), (9929023019231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671358331/1000000000 : ℝ)|^69 ≤ (14881756862801/25000000000000 : ℝ)^53
        have hw : |(671358331/1000000000 : ℝ)|=(671358331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234880547/10000000000 : ℝ)|^69 ≤ (378440227927/50000000000000 : ℝ)^53
        have hw : |(-234880547/10000000000 : ℝ)|=(234880547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(196797589/400000000 : ℝ)|^69 ≤ (9929023019231/25000000000000 : ℝ)^53
        have hw : |(196797589/400000000 : ℝ)|=(196797589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4451994339/10000000000 : ℝ)*x 0 + (1698246513/2500000000 : ℝ)*x 1 + (-238144291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4451994339/10000000000 : ℝ)^69 ≤ (34870476335303/100000000000000 : ℝ)^53 := by
    have hnat : (4451994339 : ℕ)^69*100000000000000^53 ≤ 34870476335303^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4451994339 10000000000 34870476335303 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698246513/2500000000 : ℝ)^69 ≤ (2417809415451/4000000000000 : ℝ)^53 := by
    have hnat : (1698246513 : ℕ)^69*4000000000000^53 ≤ 2417809415451^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698246513 2500000000 2417809415451 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238144291/2500000000 : ℝ)^69 ≤ (7319200401/156250000000 : ℝ)^53 := by
    have hnat : (238144291 : ℕ)^69*156250000000^53 ≤ 7319200401^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238144291 2500000000 7319200401 156250000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4451994339/10000000000 : ℝ), (1698246513/2500000000 : ℝ), (-238144291/2500000000 : ℝ)] ![(34870476335303/100000000000000 : ℝ), (2417809415451/4000000000000 : ℝ), (7319200401/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4451994339/10000000000 : ℝ)|^69 ≤ (34870476335303/100000000000000 : ℝ)^53
        have hw : |(4451994339/10000000000 : ℝ)|=(4451994339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1698246513/2500000000 : ℝ)|^69 ≤ (2417809415451/4000000000000 : ℝ)^53
        have hw : |(1698246513/2500000000 : ℝ)|=(1698246513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238144291/2500000000 : ℝ)|^69 ≤ (7319200401/156250000000 : ℝ)^53
        have hw : |(-238144291/2500000000 : ℝ)|=(238144291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s4_s4_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3499638891/5000000000 : ℝ)*x 0 + (575301913/2000000000 : ℝ)*x 1 + (2610881471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3499638891/5000000000 : ℝ)^69 ≤ (15711471248967/25000000000000 : ℝ)^53 := by
    have hnat : (3499638891 : ℕ)^69*25000000000000^53 ≤ 15711471248967^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3499638891 5000000000 15711471248967 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575301913/2000000000 : ℝ)^69 ≤ (19747156195241/100000000000000 : ℝ)^53 := by
    have hnat : (575301913 : ℕ)^69*100000000000000^53 ≤ 19747156195241^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575301913 2000000000 19747156195241 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610881471/10000000000 : ℝ)^69 ≤ (8703479399653/50000000000000 : ℝ)^53 := by
    have hnat : (2610881471 : ℕ)^69*50000000000000^53 ≤ 8703479399653^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610881471 10000000000 8703479399653 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3499638891/5000000000 : ℝ), (575301913/2000000000 : ℝ), (2610881471/10000000000 : ℝ)] ![(15711471248967/25000000000000 : ℝ), (19747156195241/100000000000000 : ℝ), (8703479399653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3499638891/5000000000 : ℝ)|^69 ≤ (15711471248967/25000000000000 : ℝ)^53
        have hw : |(3499638891/5000000000 : ℝ)|=(3499638891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(575301913/2000000000 : ℝ)|^69 ≤ (19747156195241/100000000000000 : ℝ)^53
        have hw : |(575301913/2000000000 : ℝ)|=(575301913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610881471/10000000000 : ℝ)|^69 ≤ (8703479399653/50000000000000 : ℝ)^53
        have hw : |(2610881471/10000000000 : ℝ)|=(2610881471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308063_s4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((63593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64277/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64277/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61727/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6237/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6237/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10149/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10149/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48517/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (63593/100000 : ℝ) ^ (17/4 : ℝ) ≤ (7302298567919389621/50000000000000000000 : ℝ) := by
    have hpowers : (63593/100000 : ℝ)^17 ≤ (7302298567919389621/50000000000000000000 : ℝ)^4 := by
      have hnat : (63593 : ℕ)^17*50000000000000000000^4 ≤ 7302298567919389621^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63593 100000 7302298567919389621 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63593/100000 : ℝ)) (X := (7302298567919389621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s4_corner0a : (57302298567919389621/50000000000000000000 : ℝ) ≤ (2065189399424537/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (57302298567919389621/50000000000000000000 : ℝ)^4 ≤ (2065189399424537/2000000000000000 : ℝ)^17 := by
      have hnat : (57302298567919389621 : ℕ)^4*2000000000000000^17 ≤ 2065189399424537^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57302298567919389621 50000000000000000000 2065189399424537 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2065189399424537/2000000000000000 : ℝ)) (X := (57302298567919389621/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s4_corner0b : (32302298567919389621/25000000000000000000 : ℝ) ≤ (1062152037790701/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (32302298567919389621/25000000000000000000 : ℝ)^4 ≤ (1062152037790701/1000000000000000 : ℝ)^17 := by
      have hnat : (32302298567919389621 : ℕ)^4*1000000000000000^17 ≤ 1062152037790701^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32302298567919389621 25000000000000000000 1062152037790701 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1062152037790701/1000000000000000 : ℝ)) (X := (32302298567919389621/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(65189399424537/1271860000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11822935231373/254372000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (63593/100000 : ℝ)) (alpha := (65189399424537/1271860000000000 : ℝ)) (beta := (11822935231373/254372000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (63593/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(65189399424537/1271860000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11822935231373/254372000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (64277/100000 : ℝ) ^ (17/4 : ℝ) ≤ (3056794831124764151/20000000000000000000 : ℝ) := by
    have hpowers : (64277/100000 : ℝ)^17 ≤ (3056794831124764151/20000000000000000000 : ℝ)^4 := by
      have hnat : (64277 : ℕ)^17*20000000000000000000^4 ≤ 3056794831124764151^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64277 100000 3056794831124764151 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64277/100000 : ℝ)) (X := (3056794831124764151/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s4_corner1a : (23056794831124764151/20000000000000000000 : ℝ) ≤ (2585079339843451/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (23056794831124764151/20000000000000000000 : ℝ)^4 ≤ (2585079339843451/2500000000000000 : ℝ)^17 := by
      have hnat : (23056794831124764151 : ℕ)^4*2500000000000000^17 ≤ 2585079339843451^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23056794831124764151 20000000000000000000 2585079339843451 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2585079339843451/2500000000000000 : ℝ)) (X := (23056794831124764151/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s4_corner1b : (13056794831124764151/10000000000000000000 : ℝ) ≤ (5323848277637839/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (13056794831124764151/10000000000000000000 : ℝ)^4 ≤ (5323848277637839/5000000000000000 : ℝ)^17 := by
      have hnat : (13056794831124764151 : ℕ)^4*5000000000000000^17 ≤ 5323848277637839^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13056794831124764151 10000000000000000000 5323848277637839 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5323848277637839/5000000000000000 : ℝ)) (X := (13056794831124764151/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(85079339843451/1606925000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(153689597950937/3213850000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (64277/100000 : ℝ)) (alpha := (85079339843451/1606925000000000 : ℝ)) (beta := (153689597950937/3213850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (64277/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(85079339843451/1606925000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(153689597950937/3213850000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (61727/100000 : ℝ) ^ (17/4 : ℝ) ≤ (321706238221646841/2500000000000000000 : ℝ) := by
    have hpowers : (61727/100000 : ℝ)^17 ≤ (321706238221646841/2500000000000000000 : ℝ)^4 := by
      have hnat : (61727 : ℕ)^17*2500000000000000000^4 ≤ 321706238221646841^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61727 100000 321706238221646841 2500000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61727/100000 : ℝ)) (X := (321706238221646841/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s4_corner2a : (2821706238221646841/2500000000000000000 : ℝ) ≤ (10288921004808339/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2821706238221646841/2500000000000000000 : ℝ)^4 ≤ (10288921004808339/10000000000000000 : ℝ)^17 := by
      have hnat : (2821706238221646841 : ℕ)^4*10000000000000000^17 ≤ 10288921004808339^17*2500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821706238221646841 2500000000000000000 10288921004808339 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10288921004808339/10000000000000000 : ℝ)) (X := (2821706238221646841/2500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s4_corner2b : (1571706238221646841/1250000000000000000 : ℝ) ≤ (10553649676126839/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (1571706238221646841/1250000000000000000 : ℝ)^4 ≤ (10553649676126839/10000000000000000 : ℝ)^17 := by
      have hnat : (1571706238221646841 : ℕ)^4*10000000000000000^17 ≤ 10553649676126839^17*1250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1571706238221646841 1250000000000000000 10553649676126839 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10553649676126839/10000000000000000 : ℝ)) (X := (1571706238221646841/1250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(288921004808339/6172700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(529457342637/12345400000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (61727/100000 : ℝ)) (alpha := (288921004808339/6172700000000000 : ℝ)) (beta := (529457342637/12345400000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61727/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(288921004808339/6172700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(529457342637/12345400000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-644349453/5000000000 : ℝ)*X 0 0+(220587991/400000000 : ℝ)*X 0 1+(13993603/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((1103164573/2000000000 : ℝ)*X 1 0+(-260393457/2000000000 : ℝ)*X 1 1+(5587790861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((277996873/500000000 : ℝ)*X 2 0+(1114962683/2000000000 : ℝ)*X 2 1+(-313383963/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((4374004573/10000000000 : ℝ)*X 0 0+(4315040339/10000000000 : ℝ)*X 0 1+(4211880979/10000000000 : ℝ)*X 0 2+(4374004573/10000000000 : ℝ)*X 1 0+(4315040339/10000000000 : ℝ)*X 1 1+(4211880979/10000000000 : ℝ)*X 1 2+(4374004573/10000000000 : ℝ)*X 2 0+(4315040339/10000000000 : ℝ)*X 2 1+(4211880979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-507607229/5000000000 : ℝ)*X 0 0+(4447779193/10000000000 : ℝ)*X 0 1+(6761719807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((24209403/50000000 : ℝ)*X 1 0+(-64041513/2000000000 : ℝ)*X 1 1+(6751861341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((571100643/1250000000 : ℝ)*X 2 0+(3512905713/5000000000 : ℝ)*X 2 1+(-119887241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((1102229199/2500000000 : ℝ)*X 0 0+(6171633071/10000000000 : ℝ)*X 0 1+(198951399/1000000000 : ℝ)*X 0 2+(1102229199/2500000000 : ℝ)*X 1 0+(6171633071/10000000000 : ℝ)*X 1 1+(198951399/1000000000 : ℝ)*X 1 2+(1102229199/2500000000 : ℝ)*X 2 0+(6171633071/10000000000 : ℝ)*X 2 1+(198951399/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-292798057/10000000000 : ℝ)*X 0 0+(2429367413/5000000000 : ℝ)*X 0 1+(6747383943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4483290887/10000000000 : ℝ)*X 1 0+(-62656913/625000000 : ℝ)*X 1 1+(1684382233/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((838286261/1250000000 : ℝ)*X 2 0+(4920180741/10000000000 : ℝ)*X 2 1+(-254108039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((3418138327/5000000000 : ℝ)*X 0 0+(225930627/625000000 : ℝ)*X 0 1+(1010053277/5000000000 : ℝ)*X 0 2+(3418138327/5000000000 : ℝ)*X 1 0+(225930627/625000000 : ℝ)*X 1 1+(1010053277/5000000000 : ℝ)*X 1 2+(3418138327/5000000000 : ℝ)*X 2 0+(225930627/625000000 : ℝ)*X 2 1+(1010053277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-240426483/10000000000 : ℝ)*X 0 0+(394367663/625000000 : ℝ)*X 0 1+(5351452541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((671358331/1000000000 : ℝ)*X 1 0+(-234880547/10000000000 : ℝ)*X 1 1+(196797589/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4451994339/10000000000 : ℝ)*X 2 0+(1698246513/2500000000 : ℝ)*X 2 1+(-238144291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((3499638891/5000000000 : ℝ)*X 0 0+(575301913/2000000000 : ℝ)*X 0 1+(2610881471/10000000000 : ℝ)*X 0 2+(3499638891/5000000000 : ℝ)*X 1 0+(575301913/2000000000 : ℝ)*X 1 1+(2610881471/10000000000 : ℝ)*X 1 2+(3499638891/5000000000 : ℝ)*X 2 0+(575301913/2000000000 : ℝ)*X 2 1+(2610881471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((6237/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6237/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (295923767534122012913319795867/39057780854450000000000000000000000 : ℝ) := by norm_num
    linear_combination (5576847/1000000000000 : ℝ)*(base23) + (36180109163/250000000000 : ℝ)*(base60) + (1670009136261/500000000000 : ℝ)*(major_s4_0) + (1670009136261/500000000000 : ℝ)*(major_s4_1) + (1670009136261/500000000000 : ℝ)*(major_s4_2) + (7259301/500000000000 : ℝ)*(sp_s4_0) + (12051559/1000000000000 : ℝ)*(sp_s4_6) + (4548664786031/1000000000000 : ℝ)*(sp_s4_7) + (4548665811797/1000000000000 : ℝ)*(sp_s4_8) + (4548668651669/1000000000000 : ℝ)*(sp_s4_9) + (266413923273/125000000000 : ℝ)*(sp_s4_13) + (31277141/1000000000000 : ℝ)*(sp_s4_14) + (44769977/1000000000000 : ℝ)*(sp_s4_15) + (36353257/1000000000000 : ℝ)*(sp_s4_23) + (2131323437743/1000000000000 : ℝ)*(f.failure) + (4548710581773/1000000000000 : ℝ)*(f.sum) + (510782211026498723/11669489350000000000000000000000 : ℝ)*base63 + (3279728805271/19289687500000000000000000 : ℝ)*base65 + (169656632051271/3213850000000000000000000000 : ℝ)*base66 + (284121063846471/3086350000000000000000000000 : ℝ)*base68 + (2269326537651939431/7850810222000000000000000000000 : ℝ)*base71 + (52211498908101/635930000000000000000000000 : ℝ)*base72 + (553620821816647/1606925000000000000000000000 : ℝ)*base75 + (225329153414909/317965000000000000000000000 : ℝ)*base77 + (164713588451049701/1344594493750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (56727/100000000000000000 : ℝ)*base86 + (56727/100000000000000000 : ℝ)*base88 + (56727/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10149/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10149/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (133982582135731665918185379057/19528890427225000000000000000000000 : ℝ) := by norm_num
    linear_combination (1116949/250000000000 : ℝ)*(base21) + (109047/1000000000000 : ℝ)*(base49) + (199907/1000000000000 : ℝ)*(base60) + (3371466985673/1000000000000 : ℝ)*(major_s4_0) + (3371466985673/1000000000000 : ℝ)*(major_s4_1) + (3371466985673/1000000000000 : ℝ)*(major_s4_2) + (16802041/1000000000000 : ℝ)*(sp_s4_2) + (27196333/1000000000000 : ℝ)*(sp_s4_7) + (21349751/1000000000000 : ℝ)*(sp_s4_8) + (4591513082469/1000000000000 : ℝ)*(sp_s4_14) + (4591518929051/1000000000000 : ℝ)*(sp_s4_15) + (918303801793/200000000000 : ℝ)*(sp_s4_16) + (2151365060903/1000000000000 : ℝ)*(sp_s4_20) + (6586181/250000000000 : ℝ)*(sp_s4_27) + (537847851407/250000000000 : ℝ)*(f.failure) + (2295770139401/500000000000 : ℝ)*(f.sum) + (5025523843901565649/23338978700000000000000000000000 : ℝ)*base63 + (129396184840037/617270000000000000000000000 : ℝ)*base65 + (932835533029961/3213850000000000000000000000 : ℝ)*base67 + (343930653305057/6172700000000000000000000000 : ℝ)*base69 + (28898235836291809301/78508102220000000000000000000000 : ℝ)*base71 + (123423547829209/1271860000000000000000000000 : ℝ)*base72 + (403590421053/100432812500000000000000000 : ℝ)*base75 + (54095446931541/254372000000000000000000000 : ℝ)*base77 + (10790283004143998959/21513511900000000000000000000000 : ℝ)*base79 + (17377/25000000000000000 : ℝ)*base87 + (17377/25000000000000000 : ℝ)*base89 + (17377/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48517/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (119715268767261599663868593583/39057780854450000000000000000000000 : ℝ) := by norm_num
    linear_combination (1992189/1000000000000 : ℝ)*(base15) + (182800493953/1000000000000 : ℝ)*(base40) + (3183288671541/1000000000000 : ℝ)*(major_s4_0) + (3183288671541/1000000000000 : ℝ)*(major_s4_1) + (3183288671541/1000000000000 : ℝ)*(major_s4_2) + (2603011/200000000000 : ℝ)*(sp_s4_0) + (10848269/1000000000000 : ℝ)*(sp_s4_1) + (1482603/250000000000 : ℝ)*(sp_s4_2) + (3238631/250000000000 : ℝ)*(sp_s4_9) + (21262941/1000000000000 : ℝ)*(sp_s4_20) + (867050347639/200000000000 : ℝ)*(sp_s4_21) + (541906489099/125000000000 : ℝ)*(sp_s4_22) + (2167622934157/500000000000 : ℝ)*(sp_s4_23) + (406258061039/200000000000 : ℝ)*(sp_s4_27) + (253913946017/125000000000 : ℝ)*(f.failure) + (17341059013/4000000000 : ℝ)*(f.sum) + (6199068514928336527/23338978700000000000000000000000 : ℝ)*base62 + (3885800883647/308635000000000000000000000 : ℝ)*base64 + (46295189511873/3213850000000000000000000000 : ℝ)*base66 + (542228542332031/6172700000000000000000000000 : ℝ)*base68 + (30250115147788694397/78508102220000000000000000000000 : ℝ)*base70 + (180019680594917/1271860000000000000000000000 : ℝ)*base73 + (89426480034441/401731250000000000000000000 : ℝ)*base74 + (397621370511817/1271860000000000000000000000 : ℝ)*base76 + (4863739037933178883/21513511900000000000000000000000 : ℝ)*base79 + (7587/12500000000000000 : ℝ)*base87 + (7587/12500000000000000 : ℝ)*base89 + (7587/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((63593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64277/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64277/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61727/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6237/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6237/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10149/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10149/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48517/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308063_s4 p hpa hpb X hX hprev3

#print axioms solution
