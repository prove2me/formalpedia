-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:33:27.191912+00:00
-- url     : https://prove2.me/submissions/8e1fd29c-4df8-4425-9552-1987f9ed3c62

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
theorem collision_support_c313054_s2_s2_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-15226987/125000000 : ℝ)*x 0 + (141350927/312500000 : ℝ)*x 1 + (-32113859/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15226987/125000000 : ℝ)^37 ≤ (1703822607517/25000000000000 : ℝ)^29 := by
    have hnat : (15226987 : ℕ)^37*25000000000000^29 ≤ 1703822607517^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15226987 125000000 1703822607517 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141350927/312500000 : ℝ)^37 ≤ (4542657576327/12500000000000 : ℝ)^29 := by
    have hnat : (141350927 : ℕ)^37*12500000000000^29 ≤ 4542657576327^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141350927 312500000 4542657576327 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32113859/50000000 : ℝ)^37 ≤ (56843448950079/100000000000000 : ℝ)^29 := by
    have hnat : (32113859 : ℕ)^37*100000000000000^29 ≤ 56843448950079^29*50000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32113859 50000000 56843448950079 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15226987/125000000 : ℝ), (141350927/312500000 : ℝ), (-32113859/50000000 : ℝ)] ![(1703822607517/25000000000000 : ℝ), (4542657576327/12500000000000 : ℝ), (56843448950079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15226987/125000000 : ℝ)|^37 ≤ (1703822607517/25000000000000 : ℝ)^29
        have hw : |(-15226987/125000000 : ℝ)|=(15226987/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141350927/312500000 : ℝ)|^37 ≤ (4542657576327/12500000000000 : ℝ)^29
        have hw : |(141350927/312500000 : ℝ)|=(141350927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32113859/50000000 : ℝ)|^37 ≤ (56843448950079/100000000000000 : ℝ)^29
        have hw : |(-32113859/50000000 : ℝ)|=(32113859/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2586988417/5000000000 : ℝ)*x 0 + (160667467/312500000 : ℝ)*x 1 + (1074829509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586988417/5000000000 : ℝ)^37 ≤ (43139937224771/100000000000000 : ℝ)^29 := by
    have hnat : (2586988417 : ℕ)^37*100000000000000^29 ≤ 43139937224771^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586988417 5000000000 43139937224771 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160667467/312500000 : ℝ)^37 ≤ (42793251277487/100000000000000 : ℝ)^29 := by
    have hnat : (160667467 : ℕ)^37*100000000000000^29 ≤ 42793251277487^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160667467 312500000 42793251277487 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074829509/5000000000 : ℝ)^37 ≤ (439587858723/3125000000000 : ℝ)^29 := by
    have hnat : (1074829509 : ℕ)^37*3125000000000^29 ≤ 439587858723^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074829509 5000000000 439587858723 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586988417/5000000000 : ℝ), (160667467/312500000 : ℝ), (1074829509/5000000000 : ℝ)] ![(43139937224771/100000000000000 : ℝ), (42793251277487/100000000000000 : ℝ), (439587858723/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586988417/5000000000 : ℝ)|^37 ≤ (43139937224771/100000000000000 : ℝ)^29
        have hw : |(2586988417/5000000000 : ℝ)|=(2586988417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160667467/312500000 : ℝ)|^37 ≤ (42793251277487/100000000000000 : ℝ)^29
        have hw : |(160667467/312500000 : ℝ)|=(160667467/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074829509/5000000000 : ℝ)|^37 ≤ (439587858723/3125000000000 : ℝ)^29
        have hw : |(1074829509/5000000000 : ℝ)|=(1074829509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070615923/10000000000 : ℝ)*x 0 + (818393539/2000000000 : ℝ)*x 1 + (-6895940469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070615923/10000000000 : ℝ)^37 ≤ (1156049521427/20000000000000 : ℝ)^29 := by
    have hnat : (1070615923 : ℕ)^37*20000000000000^29 ≤ 1156049521427^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070615923 10000000000 1156049521427 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (818393539/2000000000 : ℝ)^37 ≤ (31980040486019/100000000000000 : ℝ)^29 := by
    have hnat : (818393539 : ℕ)^37*100000000000000^29 ≤ 31980040486019^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818393539 2000000000 31980040486019 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6895940469/10000000000 : ℝ)^37 ≤ (2489588475777/4000000000000 : ℝ)^29 := by
    have hnat : (6895940469 : ℕ)^37*4000000000000^29 ≤ 2489588475777^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6895940469 10000000000 2489588475777 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070615923/10000000000 : ℝ), (818393539/2000000000 : ℝ), (-6895940469/10000000000 : ℝ)] ![(1156049521427/20000000000000 : ℝ), (31980040486019/100000000000000 : ℝ), (2489588475777/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070615923/10000000000 : ℝ)|^37 ≤ (1156049521427/20000000000000 : ℝ)^29
        have hw : |(-1070615923/10000000000 : ℝ)|=(1070615923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(818393539/2000000000 : ℝ)|^37 ≤ (31980040486019/100000000000000 : ℝ)^29
        have hw : |(818393539/2000000000 : ℝ)|=(818393539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6895940469/10000000000 : ℝ)|^37 ≤ (2489588475777/4000000000000 : ℝ)^29
        have hw : |(-6895940469/10000000000 : ℝ)|=(6895940469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5281280127/10000000000 : ℝ)*x 0 + (-1449036391/10000000000 : ℝ)*x 1 + (-694110339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281280127/10000000000 : ℝ)^37 ≤ (44284675513569/100000000000000 : ℝ)^29 := by
    have hnat : (5281280127 : ℕ)^37*100000000000000^29 ≤ 44284675513569^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281280127 10000000000 44284675513569 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1449036391/10000000000 : ℝ)^37 ≤ (8504580383603/100000000000000 : ℝ)^29 := by
    have hnat : (1449036391 : ℕ)^37*100000000000000^29 ≤ 8504580383603^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449036391 10000000000 8504580383603 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694110339/1250000000 : ℝ)^37 ≤ (11802686020451/25000000000000 : ℝ)^29 := by
    have hnat : (694110339 : ℕ)^37*25000000000000^29 ≤ 11802686020451^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694110339 1250000000 11802686020451 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281280127/10000000000 : ℝ), (-1449036391/10000000000 : ℝ), (-694110339/1250000000 : ℝ)] ![(44284675513569/100000000000000 : ℝ), (8504580383603/100000000000000 : ℝ), (11802686020451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281280127/10000000000 : ℝ)|^37 ≤ (44284675513569/100000000000000 : ℝ)^29
        have hw : |(5281280127/10000000000 : ℝ)|=(5281280127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1449036391/10000000000 : ℝ)|^37 ≤ (8504580383603/100000000000000 : ℝ)^29
        have hw : |(-1449036391/10000000000 : ℝ)|=(1449036391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-694110339/1250000000 : ℝ)|^37 ≤ (11802686020451/25000000000000 : ℝ)^29
        have hw : |(-694110339/1250000000 : ℝ)|=(694110339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1206452559/2500000000 : ℝ)*x 0 + (1525944861/2500000000 : ℝ)*x 1 + (80023159/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1206452559/2500000000 : ℝ)^37 ≤ (39471103850687/100000000000000 : ℝ)^29 := by
    have hnat : (1206452559 : ℕ)^37*100000000000000^29 ≤ 39471103850687^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206452559 2500000000 39471103850687 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1525944861/2500000000 : ℝ)^37 ≤ (332915257959/625000000000 : ℝ)^29 := by
    have hnat : (1525944861 : ℕ)^37*625000000000^29 ≤ 332915257959^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525944861 2500000000 332915257959 625000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80023159/625000000 : ℝ)^37 ≤ (1452490973523/20000000000000 : ℝ)^29 := by
    have hnat : (80023159 : ℕ)^37*20000000000000^29 ≤ 1452490973523^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80023159 625000000 1452490973523 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1206452559/2500000000 : ℝ), (1525944861/2500000000 : ℝ), (80023159/625000000 : ℝ)] ![(39471103850687/100000000000000 : ℝ), (332915257959/625000000000 : ℝ), (1452490973523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1206452559/2500000000 : ℝ)|^37 ≤ (39471103850687/100000000000000 : ℝ)^29
        have hw : |(1206452559/2500000000 : ℝ)|=(1206452559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1525944861/2500000000 : ℝ)|^37 ≤ (332915257959/625000000000 : ℝ)^29
        have hw : |(1525944861/2500000000 : ℝ)|=(1525944861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80023159/625000000 : ℝ)|^37 ≤ (1452490973523/20000000000000 : ℝ)^29
        have hw : |(80023159/625000000 : ℝ)|=(80023159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (998418599/2000000000 : ℝ)*x 0 + (3034696281/5000000000 : ℝ)*x 1 + (-1088194109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998418599/2000000000 : ℝ)^37 ≤ (41214525030523/100000000000000 : ℝ)^29 := by
    have hnat : (998418599 : ℕ)^37*100000000000000^29 ≤ 41214525030523^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998418599 2000000000 41214525030523 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3034696281/5000000000 : ℝ)^37 ≤ (26441934580383/50000000000000 : ℝ)^29 := by
    have hnat : (3034696281 : ℕ)^37*50000000000000^29 ≤ 26441934580383^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3034696281 5000000000 26441934580383 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088194109/10000000000 : ℝ)^37 ≤ (1475401448557/25000000000000 : ℝ)^29 := by
    have hnat : (1088194109 : ℕ)^37*25000000000000^29 ≤ 1475401448557^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088194109 10000000000 1475401448557 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(998418599/2000000000 : ℝ), (3034696281/5000000000 : ℝ), (-1088194109/10000000000 : ℝ)] ![(41214525030523/100000000000000 : ℝ), (26441934580383/50000000000000 : ℝ), (1475401448557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(998418599/2000000000 : ℝ)|^37 ≤ (41214525030523/100000000000000 : ℝ)^29
        have hw : |(998418599/2000000000 : ℝ)|=(998418599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3034696281/5000000000 : ℝ)|^37 ≤ (26441934580383/50000000000000 : ℝ)^29
        have hw : |(3034696281/5000000000 : ℝ)|=(3034696281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088194109/10000000000 : ℝ)|^37 ≤ (1475401448557/25000000000000 : ℝ)^29
        have hw : |(-1088194109/10000000000 : ℝ)|=(1088194109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-582158209/10000000000 : ℝ)*x 0 + (2236007813/5000000000 : ℝ)*x 1 + (-3416945381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (582158209/10000000000 : ℝ)^37 ≤ (2656823402749/100000000000000 : ℝ)^29 := by
    have hnat : (582158209 : ℕ)^37*100000000000000^29 ≤ 2656823402749^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582158209 10000000000 2656823402749 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236007813/5000000000 : ℝ)^37 ≤ (17908550560199/50000000000000 : ℝ)^29 := by
    have hnat : (2236007813 : ℕ)^37*50000000000000^29 ≤ 17908550560199^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236007813 5000000000 17908550560199 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3416945381/5000000000 : ℝ)^37 ≤ (1922689858103/3125000000000 : ℝ)^29 := by
    have hnat : (3416945381 : ℕ)^37*3125000000000^29 ≤ 1922689858103^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416945381 5000000000 1922689858103 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-582158209/10000000000 : ℝ), (2236007813/5000000000 : ℝ), (-3416945381/5000000000 : ℝ)] ![(2656823402749/100000000000000 : ℝ), (17908550560199/50000000000000 : ℝ), (1922689858103/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-582158209/10000000000 : ℝ)|^37 ≤ (2656823402749/100000000000000 : ℝ)^29
        have hw : |(-582158209/10000000000 : ℝ)|=(582158209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236007813/5000000000 : ℝ)|^37 ≤ (17908550560199/50000000000000 : ℝ)^29
        have hw : |(2236007813/5000000000 : ℝ)|=(2236007813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3416945381/5000000000 : ℝ)|^37 ≤ (1922689858103/3125000000000 : ℝ)^29
        have hw : |(-3416945381/5000000000 : ℝ)|=(3416945381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2460903519/5000000000 : ℝ)*x 0 + (-475907191/2500000000 : ℝ)*x 1 + (-557753221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2460903519/5000000000 : ℝ)^37 ≤ (20237806434779/50000000000000 : ℝ)^29 := by
    have hnat : (2460903519 : ℕ)^37*50000000000000^29 ≤ 20237806434779^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460903519 5000000000 20237806434779 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475907191/2500000000 : ℝ)^37 ≤ (2409219254251/20000000000000 : ℝ)^29 := by
    have hnat : (475907191 : ℕ)^37*20000000000000^29 ≤ 2409219254251^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475907191 2500000000 2409219254251 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557753221/1000000000 : ℝ)^37 ≤ (5934786355173/12500000000000 : ℝ)^29 := by
    have hnat : (557753221 : ℕ)^37*12500000000000^29 ≤ 5934786355173^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557753221 1000000000 5934786355173 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2460903519/5000000000 : ℝ), (-475907191/2500000000 : ℝ), (-557753221/1000000000 : ℝ)] ![(20237806434779/50000000000000 : ℝ), (2409219254251/20000000000000 : ℝ), (5934786355173/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2460903519/5000000000 : ℝ)|^37 ≤ (20237806434779/50000000000000 : ℝ)^29
        have hw : |(2460903519/5000000000 : ℝ)|=(2460903519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475907191/2500000000 : ℝ)|^37 ≤ (2409219254251/20000000000000 : ℝ)^29
        have hw : |(-475907191/2500000000 : ℝ)|=(475907191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-557753221/1000000000 : ℝ)|^37 ≤ (5934786355173/12500000000000 : ℝ)^29
        have hw : |(-557753221/1000000000 : ℝ)|=(557753221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (246153407/400000000 : ℝ)*x 0 + (239467631/500000000 : ℝ)*x 1 + (1255721923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246153407/400000000 : ℝ)^37 ≤ (26912200201151/50000000000000 : ℝ)^29 := by
    have hnat : (246153407 : ℕ)^37*50000000000000^29 ≤ 26912200201151^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246153407 400000000 26912200201151 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239467631/500000000 : ℝ)^37 ≤ (39091048009391/100000000000000 : ℝ)^29 := by
    have hnat : (239467631 : ℕ)^37*100000000000000^29 ≤ 39091048009391^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239467631 500000000 39091048009391 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255721923/10000000000 : ℝ)^37 ≤ (3542275789289/50000000000000 : ℝ)^29 := by
    have hnat : (1255721923 : ℕ)^37*50000000000000^29 ≤ 3542275789289^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255721923 10000000000 3542275789289 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(246153407/400000000 : ℝ), (239467631/500000000 : ℝ), (1255721923/10000000000 : ℝ)] ![(26912200201151/50000000000000 : ℝ), (39091048009391/100000000000000 : ℝ), (3542275789289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(246153407/400000000 : ℝ)|^37 ≤ (26912200201151/50000000000000 : ℝ)^29
        have hw : |(246153407/400000000 : ℝ)|=(246153407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(239467631/500000000 : ℝ)|^37 ≤ (39091048009391/100000000000000 : ℝ)^29
        have hw : |(239467631/500000000 : ℝ)|=(239467631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255721923/10000000000 : ℝ)|^37 ≤ (3542275789289/50000000000000 : ℝ)^29
        have hw : |(1255721923/10000000000 : ℝ)|=(1255721923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6038287017/10000000000 : ℝ)*x 0 + (4925594451/10000000000 : ℝ)*x 1 + (-1236478213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6038287017/10000000000 : ℝ)^37 ≤ (52538318247329/100000000000000 : ℝ)^29 := by
    have hnat : (6038287017 : ℕ)^37*100000000000000^29 ≤ 52538318247329^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038287017 10000000000 52538318247329 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925594451/10000000000 : ℝ)^37 ≤ (10128838982959/25000000000000 : ℝ)^29 := by
    have hnat : (4925594451 : ℕ)^37*25000000000000^29 ≤ 10128838982959^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925594451 10000000000 10128838982959 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236478213/10000000000 : ℝ)^37 ≤ (6946325806399/100000000000000 : ℝ)^29 := by
    have hnat : (1236478213 : ℕ)^37*100000000000000^29 ≤ 6946325806399^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236478213 10000000000 6946325806399 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6038287017/10000000000 : ℝ), (4925594451/10000000000 : ℝ), (-1236478213/10000000000 : ℝ)] ![(52538318247329/100000000000000 : ℝ), (10128838982959/25000000000000 : ℝ), (6946325806399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6038287017/10000000000 : ℝ)|^37 ≤ (52538318247329/100000000000000 : ℝ)^29
        have hw : |(6038287017/10000000000 : ℝ)|=(6038287017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4925594451/10000000000 : ℝ)|^37 ≤ (10128838982959/25000000000000 : ℝ)^29
        have hw : |(4925594451/10000000000 : ℝ)|=(4925594451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1236478213/10000000000 : ℝ)|^37 ≤ (6946325806399/100000000000000 : ℝ)^29
        have hw : |(-1236478213/10000000000 : ℝ)|=(1236478213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-186574537/5000000000 : ℝ)*x 0 + (1041455889/2000000000 : ℝ)*x 1 + (-625885991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (186574537/5000000000 : ℝ)^37 ≤ (301265138453/20000000000000 : ℝ)^29 := by
    have hnat : (186574537 : ℕ)^37*20000000000000^29 ≤ 301265138453^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186574537 5000000000 301265138453 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041455889/2000000000 : ℝ)^37 ≤ (5436815429063/12500000000000 : ℝ)^29 := by
    have hnat : (1041455889 : ℕ)^37*12500000000000^29 ≤ 5436815429063^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041455889 2000000000 5436815429063 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625885991/1000000000 : ℝ)^37 ≤ (27499575427423/50000000000000 : ℝ)^29 := by
    have hnat : (625885991 : ℕ)^37*50000000000000^29 ≤ 27499575427423^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625885991 1000000000 27499575427423 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-186574537/5000000000 : ℝ), (1041455889/2000000000 : ℝ), (-625885991/1000000000 : ℝ)] ![(301265138453/20000000000000 : ℝ), (5436815429063/12500000000000 : ℝ), (27499575427423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-186574537/5000000000 : ℝ)|^37 ≤ (301265138453/20000000000000 : ℝ)^29
        have hw : |(-186574537/5000000000 : ℝ)|=(186574537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041455889/2000000000 : ℝ)|^37 ≤ (5436815429063/12500000000000 : ℝ)^29
        have hw : |(1041455889/2000000000 : ℝ)|=(1041455889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-625885991/1000000000 : ℝ)|^37 ≤ (27499575427423/50000000000000 : ℝ)^29
        have hw : |(-625885991/1000000000 : ℝ)|=(625885991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (643768679/1000000000 : ℝ)*x 0 + (-823786721/5000000000 : ℝ)*x 1 + (-4190880633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643768679/1000000000 : ℝ)^37 ≤ (57011919358077/100000000000000 : ℝ)^29 := by
    have hnat : (643768679 : ℕ)^37*100000000000000^29 ≤ 57011919358077^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643768679 1000000000 57011919358077 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (823786721/5000000000 : ℝ)^37 ≤ (10018482967973/100000000000000 : ℝ)^29 := by
    have hnat : (823786721 : ℕ)^37*100000000000000^29 ≤ 10018482967973^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823786721 5000000000 10018482967973 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4190880633/10000000000 : ℝ)^37 ≤ (4121199708083/12500000000000 : ℝ)^29 := by
    have hnat : (4190880633 : ℕ)^37*12500000000000^29 ≤ 4121199708083^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190880633 10000000000 4121199708083 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(643768679/1000000000 : ℝ), (-823786721/5000000000 : ℝ), (-4190880633/10000000000 : ℝ)] ![(57011919358077/100000000000000 : ℝ), (10018482967973/100000000000000 : ℝ), (4121199708083/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(643768679/1000000000 : ℝ)|^37 ≤ (57011919358077/100000000000000 : ℝ)^29
        have hw : |(643768679/1000000000 : ℝ)|=(643768679/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-823786721/5000000000 : ℝ)|^37 ≤ (10018482967973/100000000000000 : ℝ)^29
        have hw : |(-823786721/5000000000 : ℝ)|=(823786721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4190880633/10000000000 : ℝ)|^37 ≤ (4121199708083/12500000000000 : ℝ)^29
        have hw : |(-4190880633/10000000000 : ℝ)|=(4190880633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (616127299/1250000000 : ℝ)*x 0 + (5308948811/10000000000 : ℝ)*x 1 + (561255487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (616127299/1250000000 : ℝ)^37 ≤ (40551292172019/100000000000000 : ℝ)^29 := by
    have hnat : (616127299 : ℕ)^37*100000000000000^29 ≤ 40551292172019^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616127299 1250000000 40551292172019 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5308948811/10000000000 : ℝ)^37 ≤ (44580899221907/100000000000000 : ℝ)^29 := by
    have hnat : (5308948811 : ℕ)^37*100000000000000^29 ≤ 44580899221907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5308948811 10000000000 44580899221907 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561255487/2500000000 : ℝ)^37 ≤ (14867808584029/100000000000000 : ℝ)^29 := by
    have hnat : (561255487 : ℕ)^37*100000000000000^29 ≤ 14867808584029^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561255487 2500000000 14867808584029 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(616127299/1250000000 : ℝ), (5308948811/10000000000 : ℝ), (561255487/2500000000 : ℝ)] ![(40551292172019/100000000000000 : ℝ), (44580899221907/100000000000000 : ℝ), (14867808584029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(616127299/1250000000 : ℝ)|^37 ≤ (40551292172019/100000000000000 : ℝ)^29
        have hw : |(616127299/1250000000 : ℝ)|=(616127299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5308948811/10000000000 : ℝ)|^37 ≤ (44580899221907/100000000000000 : ℝ)^29
        have hw : |(5308948811/10000000000 : ℝ)|=(5308948811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561255487/2500000000 : ℝ)|^37 ≤ (14867808584029/100000000000000 : ℝ)^29
        have hw : |(561255487/2500000000 : ℝ)|=(561255487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313054_s2_s2_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5842199843/10000000000 : ℝ)*x 0 + (482907717/1000000000 : ℝ)*x 1 + (-103817911/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5842199843/10000000000 : ℝ)^37 ≤ (3148210124293/6250000000000 : ℝ)^29 := by
    have hnat : (5842199843 : ℕ)^37*6250000000000^29 ≤ 3148210124293^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5842199843 10000000000 3148210124293 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482907717/1000000000 : ℝ)^37 ≤ (39505199083681/100000000000000 : ℝ)^29 := by
    have hnat : (482907717 : ℕ)^37*100000000000000^29 ≤ 39505199083681^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482907717 1000000000 39505199083681 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103817911/625000000 : ℝ)^37 ≤ (316357466137/3125000000000 : ℝ)^29 := by
    have hnat : (103817911 : ℕ)^37*3125000000000^29 ≤ 316357466137^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103817911 625000000 316357466137 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5842199843/10000000000 : ℝ), (482907717/1000000000 : ℝ), (-103817911/625000000 : ℝ)] ![(3148210124293/6250000000000 : ℝ), (39505199083681/100000000000000 : ℝ), (316357466137/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5842199843/10000000000 : ℝ)|^37 ≤ (3148210124293/6250000000000 : ℝ)^29
        have hw : |(5842199843/10000000000 : ℝ)|=(5842199843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482907717/1000000000 : ℝ)|^37 ≤ (39505199083681/100000000000000 : ℝ)^29
        have hw : |(482907717/1000000000 : ℝ)|=(482907717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103817911/625000000 : ℝ)|^37 ≤ (316357466137/3125000000000 : ℝ)^29
        have hw : |(-103817911/625000000 : ℝ)|=(103817911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313054_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((29801/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29801/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6267/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6267/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-51201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-51201/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8733/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8733/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36669/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36669/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2409/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2409/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (29801/50000 : ℝ) ^ (73/16 : ℝ) ≤ (943251601375244203/10000000000000000000 : ℝ) := by
    have hpowers : (29801/50000 : ℝ)^73 ≤ (943251601375244203/10000000000000000000 : ℝ)^16 := by
      have hnat : (29801 : ℕ)^73*10000000000000000000^16 ≤ 943251601375244203^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29801 50000 943251601375244203 10000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29801/50000 : ℝ)) (X := (943251601375244203/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (10943251601375244203/10000000000000000000 : ℝ) ≤ (203990538828253/200000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (10943251601375244203/10000000000000000000 : ℝ)^16 ≤ (203990538828253/200000000000000 : ℝ)^73 := by
      have hnat : (10943251601375244203 : ℕ)^16*200000000000000^73 ≤ 203990538828253^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10943251601375244203 10000000000000000000 203990538828253 200000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (203990538828253/200000000000000 : ℝ)) (X := (10943251601375244203/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (5943251601375244203/5000000000000000000 : ℝ) ≤ (10386045390284489/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (5943251601375244203/5000000000000000000 : ℝ)^16 ≤ (10386045390284489/10000000000000000 : ℝ)^73 := by
      have hnat : (5943251601375244203 : ℕ)^16*10000000000000000^73 ≤ 10386045390284489^73*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5943251601375244203 5000000000000000000 10386045390284489 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10386045390284489/10000000000000000 : ℝ)) (X := (5943251601375244203/5000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3990538828253/119204000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(186518448871839/5960200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (29801/50000 : ℝ)) (alpha := (3990538828253/119204000000000 : ℝ)) (beta := (186518448871839/5960200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (29801/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3990538828253/119204000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(186518448871839/5960200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (6267/10000 : ℝ) ^ (73/16 : ℝ) ≤ (5930002294479096337/50000000000000000000 : ℝ) := by
    have hpowers : (6267/10000 : ℝ)^73 ≤ (5930002294479096337/50000000000000000000 : ℝ)^16 := by
      have hnat : (6267 : ℕ)^73*50000000000000000000^16 ≤ 5930002294479096337^16*10000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6267 10000 5930002294479096337 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6267/10000 : ℝ)) (X := (5930002294479096337/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (55930002294479096337/50000000000000000000 : ℝ) ≤ (1024869235075731/1000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (55930002294479096337/50000000000000000000 : ℝ)^16 ≤ (1024869235075731/1000000000000000 : ℝ)^73 := by
      have hnat : (55930002294479096337 : ℕ)^16*1000000000000000^73 ≤ 1024869235075731^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55930002294479096337 50000000000000000000 1024869235075731 1000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1024869235075731/1000000000000000 : ℝ)) (X := (55930002294479096337/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (30930002294479096337/25000000000000000000 : ℝ) ≤ (10477575754766933/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (30930002294479096337/25000000000000000000 : ℝ)^16 ≤ (10477575754766933/10000000000000000 : ℝ)^73 := by
      have hnat : (30930002294479096337 : ℕ)^16*10000000000000000^73 ≤ 10477575754766933^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30930002294479096337 25000000000000000000 10477575754766933 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10477575754766933/10000000000000000 : ℝ)) (X := (30930002294479096337/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(24869235075731/626700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(228883404009623/6267000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (6267/10000 : ℝ)) (alpha := (24869235075731/626700000000000 : ℝ)) (beta := (228883404009623/6267000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6267/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(24869235075731/626700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(228883404009623/6267000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (51201/100000 : ℝ) ^ (73/16 : ℝ) ≤ (188643953022353161/4000000000000000000 : ℝ) := by
    have hpowers : (51201/100000 : ℝ)^73 ≤ (188643953022353161/4000000000000000000 : ℝ)^16 := by
      have hnat : (51201 : ℕ)^73*4000000000000000000^16 ≤ 188643953022353161^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51201 100000 188643953022353161 4000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51201/100000 : ℝ)) (X := (188643953022353161/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (4188643953022353161/4000000000000000000 : ℝ) ≤ (10101514940974797/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (4188643953022353161/4000000000000000000 : ℝ)^16 ≤ (10101514940974797/10000000000000000 : ℝ)^73 := by
      have hnat : (4188643953022353161 : ℕ)^16*10000000000000000^73 ≤ 10101514940974797^73*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4188643953022353161 4000000000000000000 10101514940974797 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10101514940974797/10000000000000000 : ℝ)) (X := (4188643953022353161/4000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (2188643953022353161/2000000000000000000 : ℝ) ≤ (10199520437819707/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2188643953022353161/2000000000000000000 : ℝ)^16 ≤ (10199520437819707/10000000000000000 : ℝ)^73 := by
      have hnat : (2188643953022353161 : ℕ)^16*10000000000000000^73 ≤ 10199520437819707^73*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2188643953022353161 2000000000000000000 10199520437819707 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10199520437819707/10000000000000000 : ℝ)) (X := (2188643953022353161/2000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(101514940974797/5120100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9800549684491/512010000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (51201/100000 : ℝ)) (alpha := (101514940974797/5120100000000000 : ℝ)) (beta := (9800549684491/512010000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (51201/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(101514940974797/5120100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9800549684491/512010000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-15226987/125000000 : ℝ)*X 0 0+(141350927/312500000 : ℝ)*X 0 1+(-32113859/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2586988417/5000000000 : ℝ)*X 2 0+(160667467/312500000 : ℝ)*X 2 1+(1074829509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1070615923/10000000000 : ℝ)*X 0 0+(818393539/2000000000 : ℝ)*X 0 1+(-6895940469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5281280127/10000000000 : ℝ)*X 1 0+(-1449036391/10000000000 : ℝ)*X 1 1+(-694110339/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1206452559/2500000000 : ℝ)*X 2 0+(1525944861/2500000000 : ℝ)*X 2 1+(80023159/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((998418599/2000000000 : ℝ)*X 0 0+(3034696281/5000000000 : ℝ)*X 0 1+(-1088194109/10000000000 : ℝ)*X 0 2+(998418599/2000000000 : ℝ)*X 1 0+(3034696281/5000000000 : ℝ)*X 1 1+(-1088194109/10000000000 : ℝ)*X 1 2+(998418599/2000000000 : ℝ)*X 2 0+(3034696281/5000000000 : ℝ)*X 2 1+(-1088194109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-582158209/10000000000 : ℝ)*X 0 0+(2236007813/5000000000 : ℝ)*X 0 1+(-3416945381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2460903519/5000000000 : ℝ)*X 1 0+(-475907191/2500000000 : ℝ)*X 1 1+(-557753221/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((246153407/400000000 : ℝ)*X 2 0+(239467631/500000000 : ℝ)*X 2 1+(1255721923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((6038287017/10000000000 : ℝ)*X 0 0+(4925594451/10000000000 : ℝ)*X 0 1+(-1236478213/10000000000 : ℝ)*X 0 2+(6038287017/10000000000 : ℝ)*X 1 0+(4925594451/10000000000 : ℝ)*X 1 1+(-1236478213/10000000000 : ℝ)*X 1 2+(6038287017/10000000000 : ℝ)*X 2 0+(4925594451/10000000000 : ℝ)*X 2 1+(-1236478213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-186574537/5000000000 : ℝ)*X 0 0+(1041455889/2000000000 : ℝ)*X 0 1+(-625885991/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((643768679/1000000000 : ℝ)*X 1 0+(-823786721/5000000000 : ℝ)*X 1 1+(-4190880633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((616127299/1250000000 : ℝ)*X 2 0+(5308948811/10000000000 : ℝ)*X 2 1+(561255487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((5842199843/10000000000 : ℝ)*X 0 0+(482907717/1000000000 : ℝ)*X 0 1+(-103817911/625000000 : ℝ)*X 0 2+(5842199843/10000000000 : ℝ)*X 1 0+(482907717/1000000000 : ℝ)*X 1 1+(-103817911/625000000 : ℝ)*X 1 2+(5842199843/10000000000 : ℝ)*X 2 0+(482907717/1000000000 : ℝ)*X 2 1+(-103817911/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((8733/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8733/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (200787153557376302694824039/15563572250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1030637/200000000000 : ℝ)*(base23) + (656161947301/1000000000000 : ℝ)*(base39) + (3848157/1000000000000 : ℝ)*(base50) + (7091503311/15625000000 : ℝ)*(base60) + (2699066594183/500000000000 : ℝ)*(major_s2_0) + (2699066594183/500000000000 : ℝ)*(major_s2_1) + (2699066594183/500000000000 : ℝ)*(major_s2_2) + (7611219216839/1000000000000 : ℝ)*(sp_s2_7) + (3805556169759/500000000000 : ℝ)*(sp_s2_8) + (7611197509689/1000000000000 : ℝ)*(sp_s2_9) + (3184983620199/1000000000000 : ℝ)*(sp_s2_13) + (29619661/500000000000 : ℝ)*(sp_s2_14) + (166116643/1000000000000 : ℝ)*(sp_s2_15) + (37896643/500000000000 : ℝ)*(sp_s2_23) + (3184983620199/1000000000000 : ℝ)*(f.failure) + (47570490351/6250000000 : ℝ)*(f.sum) + (47710954806064079/267397222500000000000000000000 : ℝ)*base63 + (347240658957809/512010000000000000000000000 : ℝ)*base64 + (3920288485066091/3133500000000000000000000000 : ℝ)*base67 + (1232442320142637/1280025000000000000000000000 : ℝ)*base68 + (1762433999332866953/15258410010000000000000000000000 : ℝ)*base71 + (2367566781853907/2980100000000000000000000000 : ℝ)*base73 + (29499903674881/156675000000000000000000000 : ℝ)*base74 + (9393794134841/59602000000000000000000000 : ℝ)*base76 + (4252996179061461017/11672679187500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (67913/100000000000000000 : ℝ)*base87 + (67913/100000000000000000 : ℝ)*base89 + (67913/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36669/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36669/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (176608281691405509483671438017/17708232506050000000000000000000000 : ℝ) := by norm_num
    linear_combination (296656444321/500000000000 : ℝ)*(base39) + (530229/250000000000 : ℝ)*(base49) + (41255974683/250000000000 : ℝ)*(base60) + (1085390966487/200000000000 : ℝ)*(major_s2_0) + (1085390966487/200000000000 : ℝ)*(major_s2_1) + (1085390966487/200000000000 : ℝ)*(major_s2_2) + (12265921/125000000000 : ℝ)*(sp_s2_0) + (99189611/1000000000000 : ℝ)*(sp_s2_8) + (7651783721149/1000000000000 : ℝ)*(sp_s2_14) + (1530363661321/200000000000 : ℝ)*(sp_s2_15) + (7651917496217/1000000000000 : ℝ)*(sp_s2_16) + (3201740745781/1000000000000 : ℝ)*(sp_s2_20) + (356477/10000000000 : ℝ)*(sp_s2_21) + (124049229/500000000000 : ℝ)*(sp_s2_27) + (3201988844239/1000000000000 : ℝ)*(f.failure) + (7651917496217/1000000000000 : ℝ)*(f.sum) + (3220547198728351/71305926000000000000000000000 : ℝ)*base62 + (10520608714793/21333750000000000000000000 : ℝ)*base64 + (116282213354753/417800000000000000000000000 : ℝ)*base67 + (841439100341/341340000000000000000000000 : ℝ)*base69 + (234514038907734833/2034454668000000000000000000000 : ℝ)*base70 + (95872454582033/238408000000000000000000000 : ℝ)*base73 + (23519045436589/41780000000000000000000000 : ℝ)*base74 + (291867531084587/596020000000000000000000000 : ℝ)*base76 + (894732318770099709/6225428900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (35393/100000000000000000 : ℝ)*base87 + (35393/100000000000000000 : ℝ)*base89 + (35393/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2409/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2409/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (68145734667676223001272551863/7083293002420000000000000000000000 : ℝ) := by norm_num
    linear_combination (481060922403/500000000000 : ℝ)*(base39) + (2354741/1000000000000 : ℝ)*(base40) + (2084613/1000000000000 : ℝ)*(base50) + (34397317857/8000000000 : ℝ)*(major_s2_0) + (34397317857/8000000000 : ℝ)*(major_s2_1) + (34397317857/8000000000 : ℝ)*(major_s2_2) + (2896419/1000000000000 : ℝ)*(sp_s2_0) + (23039/976562500 : ℝ)*(sp_s2_2) + (32851241/1000000000000 : ℝ)*(sp_s2_9) + (89148281/500000000000 : ℝ)*(sp_s2_20) + (6062453434571/1000000000000 : ℝ)*(sp_s2_21) + (606245633099/100000000000 : ℝ)*(sp_s2_22) + (6062399887813/1000000000000 : ℝ)*(sp_s2_23) + (2536691629819/1000000000000 : ℝ)*(sp_s2_27) + (2536869926381/1000000000000 : ℝ)*(f.failure) + (606245633099/100000000000 : ℝ)*(f.sum) + (63995870310242863/178264815000000000000000000000 : ℝ)*base62 + (5413376163019/42667500000000000000000000 : ℝ)*base64 + (133531323317/668480000000000000000000 : ℝ)*base66 + (24913855723939/341340000000000000000000000 : ℝ)*base68 + (3492790093721977783/10172273340000000000000000000000 : ℝ)*base70 + (93297739090011/238408000000000000000000000 : ℝ)*base73 + (16719924332501/41780000000000000000000000 : ℝ)*base74 + (184787175523921/596020000000000000000000000 : ℝ)*base76 + (86847383930896367/1245085780000000000000000000000 : ℝ)*base79 + (36547/100000000000000000 : ℝ)*base87 + (36547/100000000000000000 : ℝ)*base89 + (36547/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((29801/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29801/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6267/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6267/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-51201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-51201/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8733/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8733/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36669/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36669/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2409/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2409/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313054_s2 p hpa hpb X hX hprev1

#print axioms solution
