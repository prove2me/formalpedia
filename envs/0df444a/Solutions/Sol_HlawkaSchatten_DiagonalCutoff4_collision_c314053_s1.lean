-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:49.280272+00:00
-- url     : https://prove2.me/submissions/b2237a04-fc86-4022-8fbd-fe645030d6d2

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
theorem collision_support_c314053_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-436436743/2500000000 : ℝ)*x 0 + (1039827337/2000000000 : ℝ)*x 1 + (5390182973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436436743/2500000000 : ℝ)^75 ≤ (10874690449479/100000000000000 : ℝ)^59 := by
    have hnat : (436436743 : ℕ)^75*100000000000000^59 ≤ 10874690449479^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436436743 2500000000 10874690449479 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039827337/2000000000 : ℝ)^75 ≤ (21770361581607/50000000000000 : ℝ)^59 := by
    have hnat : (1039827337 : ℕ)^75*50000000000000^59 ≤ 21770361581607^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039827337 2000000000 21770361581607 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390182973/10000000000 : ℝ)^75 ≤ (45584586371249/100000000000000 : ℝ)^59 := by
    have hnat : (5390182973 : ℕ)^75*100000000000000^59 ≤ 45584586371249^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390182973 10000000000 45584586371249 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436436743/2500000000 : ℝ), (1039827337/2000000000 : ℝ), (5390182973/10000000000 : ℝ)] ![(10874690449479/100000000000000 : ℝ), (21770361581607/50000000000000 : ℝ), (45584586371249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436436743/2500000000 : ℝ)|^75 ≤ (10874690449479/100000000000000 : ℝ)^59
        have hw : |(-436436743/2500000000 : ℝ)|=(436436743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039827337/2000000000 : ℝ)|^75 ≤ (21770361581607/50000000000000 : ℝ)^59
        have hw : |(1039827337/2000000000 : ℝ)|=(1039827337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390182973/10000000000 : ℝ)|^75 ≤ (45584586371249/100000000000000 : ℝ)^59
        have hw : |(5390182973/10000000000 : ℝ)|=(5390182973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (904271757/2000000000 : ℝ)*x 0 + (-134552333/1250000000 : ℝ)*x 1 + (3242408689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904271757/2000000000 : ℝ)^75 ≤ (7291427906257/20000000000000 : ℝ)^59 := by
    have hnat : (904271757 : ℕ)^75*20000000000000^59 ≤ 7291427906257^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904271757 2000000000 7291427906257 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134552333/1250000000 : ℝ)^75 ≤ (588122306463/10000000000000 : ℝ)^59 := by
    have hnat : (134552333 : ℕ)^75*10000000000000^59 ≤ 588122306463^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134552333 1250000000 588122306463 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3242408689/5000000000 : ℝ)^75 ≤ (576616373819/1000000000000 : ℝ)^59 := by
    have hnat : (3242408689 : ℕ)^75*1000000000000^59 ≤ 576616373819^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3242408689 5000000000 576616373819 1000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(904271757/2000000000 : ℝ), (-134552333/1250000000 : ℝ), (3242408689/5000000000 : ℝ)] ![(7291427906257/20000000000000 : ℝ), (588122306463/10000000000000 : ℝ), (576616373819/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(904271757/2000000000 : ℝ)|^75 ≤ (7291427906257/20000000000000 : ℝ)^59
        have hw : |(904271757/2000000000 : ℝ)|=(904271757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134552333/1250000000 : ℝ)|^75 ≤ (588122306463/10000000000000 : ℝ)^59
        have hw : |(-134552333/1250000000 : ℝ)|=(134552333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3242408689/5000000000 : ℝ)|^75 ≤ (576616373819/1000000000000 : ℝ)^59
        have hw : |(3242408689/5000000000 : ℝ)|=(3242408689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (90942783/200000000 : ℝ)*x 0 + (6504420027/10000000000 : ℝ)*x 1 + (-1005788911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90942783/200000000 : ℝ)^75 ≤ (1836079584299/5000000000000 : ℝ)^59 := by
    have hnat : (90942783 : ℕ)^75*5000000000000^59 ≤ 1836079584299^59*200000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90942783 200000000 1836079584299 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6504420027/10000000000 : ℝ)^75 ≤ (14470824823689/25000000000000 : ℝ)^59 := by
    have hnat : (6504420027 : ℕ)^75*25000000000000^59 ≤ 14470824823689^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6504420027 10000000000 14470824823689 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005788911/10000000000 : ℝ)^75 ≤ (5395109011911/100000000000000 : ℝ)^59 := by
    have hnat : (1005788911 : ℕ)^75*100000000000000^59 ≤ 5395109011911^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005788911 10000000000 5395109011911 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90942783/200000000 : ℝ), (6504420027/10000000000 : ℝ), (-1005788911/10000000000 : ℝ)] ![(1836079584299/5000000000000 : ℝ), (14470824823689/25000000000000 : ℝ), (5395109011911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90942783/200000000 : ℝ)|^75 ≤ (1836079584299/5000000000000 : ℝ)^59
        have hw : |(90942783/200000000 : ℝ)|=(90942783/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6504420027/10000000000 : ℝ)|^75 ≤ (14470824823689/25000000000000 : ℝ)^59
        have hw : |(6504420027/10000000000 : ℝ)|=(6504420027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1005788911/10000000000 : ℝ)|^75 ≤ (5395109011911/100000000000000 : ℝ)^59
        have hw : |(-1005788911/10000000000 : ℝ)|=(1005788911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7394263907/10000000000 : ℝ)*x 0 + (1241429871/5000000000 : ℝ)*x 1 + (2230975029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7394263907/10000000000 : ℝ)^75 ≤ (17032603740013/25000000000000 : ℝ)^59 := by
    have hnat : (7394263907 : ℕ)^75*25000000000000^59 ≤ 17032603740013^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7394263907 10000000000 17032603740013 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1241429871/5000000000 : ℝ)^75 ≤ (1701654646003/10000000000000 : ℝ)^59 := by
    have hnat : (1241429871 : ℕ)^75*10000000000000^59 ≤ 1701654646003^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241429871 5000000000 1701654646003 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230975029/10000000000 : ℝ)^75 ≤ (7426519278669/50000000000000 : ℝ)^59 := by
    have hnat : (2230975029 : ℕ)^75*50000000000000^59 ≤ 7426519278669^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230975029 10000000000 7426519278669 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7394263907/10000000000 : ℝ), (1241429871/5000000000 : ℝ), (2230975029/10000000000 : ℝ)] ![(17032603740013/25000000000000 : ℝ), (1701654646003/10000000000000 : ℝ), (7426519278669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7394263907/10000000000 : ℝ)|^75 ≤ (17032603740013/25000000000000 : ℝ)^59
        have hw : |(7394263907/10000000000 : ℝ)|=(7394263907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1241429871/5000000000 : ℝ)|^75 ≤ (1701654646003/10000000000000 : ℝ)^59
        have hw : |(1241429871/5000000000 : ℝ)|=(1241429871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2230975029/10000000000 : ℝ)|^75 ≤ (7426519278669/50000000000000 : ℝ)^59
        have hw : |(2230975029/10000000000 : ℝ)|=(2230975029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1816602491/10000000000 : ℝ)*x 0 + (3815996601/10000000000 : ℝ)*x 1 + (827289981/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1816602491/10000000000 : ℝ)^75 ≤ (2859705063273/25000000000000 : ℝ)^59 := by
    have hnat : (1816602491 : ℕ)^75*25000000000000^59 ≤ 2859705063273^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816602491 10000000000 2859705063273 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3815996601/10000000000 : ℝ)^75 ≤ (14693178024617/50000000000000 : ℝ)^59 := by
    have hnat : (3815996601 : ℕ)^75*50000000000000^59 ≤ 14693178024617^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3815996601 10000000000 14693178024617 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827289981/1250000000 : ℝ)^75 ≤ (3698426480283/6250000000000 : ℝ)^59 := by
    have hnat : (827289981 : ℕ)^75*6250000000000^59 ≤ 3698426480283^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827289981 1250000000 3698426480283 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1816602491/10000000000 : ℝ), (3815996601/10000000000 : ℝ), (827289981/1250000000 : ℝ)] ![(2859705063273/25000000000000 : ℝ), (14693178024617/50000000000000 : ℝ), (3698426480283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1816602491/10000000000 : ℝ)|^75 ≤ (2859705063273/25000000000000 : ℝ)^59
        have hw : |(-1816602491/10000000000 : ℝ)|=(1816602491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3815996601/10000000000 : ℝ)|^75 ≤ (14693178024617/50000000000000 : ℝ)^59
        have hw : |(3815996601/10000000000 : ℝ)|=(3815996601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827289981/1250000000 : ℝ)|^75 ≤ (3698426480283/6250000000000 : ℝ)^59
        have hw : |(827289981/1250000000 : ℝ)|=(827289981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (43820477/125000000 : ℝ)*x 0 + (-497555099/10000000000 : ℝ)*x 1 + (95913293/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43820477/125000000 : ℝ)^75 ≤ (6595596869109/25000000000000 : ℝ)^59 := by
    have hnat : (43820477 : ℕ)^75*25000000000000^59 ≤ 6595596869109^59*125000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43820477 125000000 6595596869109 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497555099/10000000000 : ℝ)^75 ≤ (275646316059/12500000000000 : ℝ)^59 := by
    have hnat : (497555099 : ℕ)^75*12500000000000^59 ≤ 275646316059^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497555099 10000000000 275646316059 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95913293/125000000 : ℝ)^75 ≤ (3570622098917/5000000000000 : ℝ)^59 := by
    have hnat : (95913293 : ℕ)^75*5000000000000^59 ≤ 3570622098917^59*125000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95913293 125000000 3570622098917 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43820477/125000000 : ℝ), (-497555099/10000000000 : ℝ), (95913293/125000000 : ℝ)] ![(6595596869109/25000000000000 : ℝ), (275646316059/12500000000000 : ℝ), (3570622098917/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43820477/125000000 : ℝ)|^75 ≤ (6595596869109/25000000000000 : ℝ)^59
        have hw : |(43820477/125000000 : ℝ)|=(43820477/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-497555099/10000000000 : ℝ)|^75 ≤ (275646316059/12500000000000 : ℝ)^59
        have hw : |(-497555099/10000000000 : ℝ)|=(497555099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95913293/125000000 : ℝ)|^75 ≤ (3570622098917/5000000000000 : ℝ)^59
        have hw : |(95913293/125000000 : ℝ)|=(95913293/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1766596339/5000000000 : ℝ)*x 0 + (310873207/400000000 : ℝ)*x 1 + (-217626527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1766596339/5000000000 : ℝ)^75 ≤ (5329254021907/20000000000000 : ℝ)^59 := by
    have hnat : (1766596339 : ℕ)^75*20000000000000^59 ≤ 5329254021907^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766596339 5000000000 5329254021907 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310873207/400000000 : ℝ)^75 ≤ (72582965167061/100000000000000 : ℝ)^59 := by
    have hnat : (310873207 : ℕ)^75*100000000000000^59 ≤ 72582965167061^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310873207 400000000 72582965167061 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217626527/10000000000 : ℝ)^75 ≤ (192691176447/25000000000000 : ℝ)^59 := by
    have hnat : (217626527 : ℕ)^75*25000000000000^59 ≤ 192691176447^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217626527 10000000000 192691176447 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1766596339/5000000000 : ℝ), (310873207/400000000 : ℝ), (-217626527/10000000000 : ℝ)] ![(5329254021907/20000000000000 : ℝ), (72582965167061/100000000000000 : ℝ), (192691176447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1766596339/5000000000 : ℝ)|^75 ≤ (5329254021907/20000000000000 : ℝ)^59
        have hw : |(1766596339/5000000000 : ℝ)|=(1766596339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(310873207/400000000 : ℝ)|^75 ≤ (72582965167061/100000000000000 : ℝ)^59
        have hw : |(310873207/400000000 : ℝ)|=(310873207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217626527/10000000000 : ℝ)|^75 ≤ (192691176447/25000000000000 : ℝ)^59
        have hw : |(-217626527/10000000000 : ℝ)|=(217626527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (96634017/156250000 : ℝ)*x 0 + (1308797397/2500000000 : ℝ)*x 1 + (210718233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96634017/156250000 : ℝ)^75 ≤ (54289533620101/100000000000000 : ℝ)^59 := by
    have hnat : (96634017 : ℕ)^75*100000000000000^59 ≤ 54289533620101^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96634017 156250000 54289533620101 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308797397/2500000000 : ℝ)^75 ≤ (43924891322159/100000000000000 : ℝ)^59 := by
    have hnat : (1308797397 : ℕ)^75*100000000000000^59 ≤ 43924891322159^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308797397 2500000000 43924891322159 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210718233/5000000000 : ℝ)^75 ≤ (1785575045653/100000000000000 : ℝ)^59 := by
    have hnat : (210718233 : ℕ)^75*100000000000000^59 ≤ 1785575045653^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210718233 5000000000 1785575045653 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(96634017/156250000 : ℝ), (1308797397/2500000000 : ℝ), (210718233/5000000000 : ℝ)] ![(54289533620101/100000000000000 : ℝ), (43924891322159/100000000000000 : ℝ), (1785575045653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(96634017/156250000 : ℝ)|^75 ≤ (54289533620101/100000000000000 : ℝ)^59
        have hw : |(96634017/156250000 : ℝ)|=(96634017/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308797397/2500000000 : ℝ)|^75 ≤ (43924891322159/100000000000000 : ℝ)^59
        have hw : |(1308797397/2500000000 : ℝ)|=(1308797397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210718233/5000000000 : ℝ)|^75 ≤ (1785575045653/100000000000000 : ℝ)^59
        have hw : |(210718233/5000000000 : ℝ)|=(210718233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-531776457/5000000000 : ℝ)*x 0 + (973274911/2500000000 : ℝ)*x 1 + (7044886147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531776457/5000000000 : ℝ)^75 ≤ (579201085011/10000000000000 : ℝ)^59 := by
    have hnat : (531776457 : ℕ)^75*10000000000000^59 ≤ 579201085011^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531776457 5000000000 579201085011 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973274911/2500000000 : ℝ)^75 ≤ (15071595307519/50000000000000 : ℝ)^59 := by
    have hnat : (973274911 : ℕ)^75*50000000000000^59 ≤ 15071595307519^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973274911 2500000000 15071595307519 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7044886147/10000000000 : ℝ)^75 ≤ (32032399257279/50000000000000 : ℝ)^59 := by
    have hnat : (7044886147 : ℕ)^75*50000000000000^59 ≤ 32032399257279^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7044886147 10000000000 32032399257279 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531776457/5000000000 : ℝ), (973274911/2500000000 : ℝ), (7044886147/10000000000 : ℝ)] ![(579201085011/10000000000000 : ℝ), (15071595307519/50000000000000 : ℝ), (32032399257279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531776457/5000000000 : ℝ)|^75 ≤ (579201085011/10000000000000 : ℝ)^59
        have hw : |(-531776457/5000000000 : ℝ)|=(531776457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973274911/2500000000 : ℝ)|^75 ≤ (15071595307519/50000000000000 : ℝ)^59
        have hw : |(973274911/2500000000 : ℝ)|=(973274911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7044886147/10000000000 : ℝ)|^75 ≤ (32032399257279/50000000000000 : ℝ)^59
        have hw : |(7044886147/10000000000 : ℝ)|=(7044886147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2442385733/10000000000 : ℝ)*x 0 + (-210254939/2000000000 : ℝ)*x 1 + (2048433087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2442385733/10000000000 : ℝ)^75 ≤ (4166177697309/25000000000000 : ℝ)^59 := by
    have hnat : (2442385733 : ℕ)^75*25000000000000^59 ≤ 4166177697309^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2442385733 10000000000 4166177697309 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210254939/2000000000 : ℝ)^75 ≤ (5707145068983/100000000000000 : ℝ)^59 := by
    have hnat : (210254939 : ℕ)^75*100000000000000^59 ≤ 5707145068983^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210254939 2000000000 5707145068983 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048433087/2500000000 : ℝ)^75 ≤ (19407036031201/25000000000000 : ℝ)^59 := by
    have hnat : (2048433087 : ℕ)^75*25000000000000^59 ≤ 19407036031201^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048433087 2500000000 19407036031201 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2442385733/10000000000 : ℝ), (-210254939/2000000000 : ℝ), (2048433087/2500000000 : ℝ)] ![(4166177697309/25000000000000 : ℝ), (5707145068983/100000000000000 : ℝ), (19407036031201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2442385733/10000000000 : ℝ)|^75 ≤ (4166177697309/25000000000000 : ℝ)^59
        have hw : |(2442385733/10000000000 : ℝ)|=(2442385733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210254939/2000000000 : ℝ)|^75 ≤ (5707145068983/100000000000000 : ℝ)^59
        have hw : |(-210254939/2000000000 : ℝ)|=(210254939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2048433087/2500000000 : ℝ)|^75 ≤ (19407036031201/25000000000000 : ℝ)^59
        have hw : |(2048433087/2500000000 : ℝ)|=(2048433087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6262281451/10000000000 : ℝ)*x 0 + (2581947883/5000000000 : ℝ)*x 1 + (-100239001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6262281451/10000000000 : ℝ)^75 ≤ (55158089494519/100000000000000 : ℝ)^59 := by
    have hnat : (6262281451 : ℕ)^75*100000000000000^59 ≤ 55158089494519^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6262281451 10000000000 55158089494519 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2581947883/5000000000 : ℝ)^75 ≤ (43165904778753/100000000000000 : ℝ)^59 := by
    have hnat : (2581947883 : ℕ)^75*100000000000000^59 ≤ 43165904778753^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581947883 5000000000 43165904778753 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100239001/2500000000 : ℝ)^75 ≤ (1676005706131/100000000000000 : ℝ)^59 := by
    have hnat : (100239001 : ℕ)^75*100000000000000^59 ≤ 1676005706131^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100239001 2500000000 1676005706131 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6262281451/10000000000 : ℝ), (2581947883/5000000000 : ℝ), (-100239001/2500000000 : ℝ)] ![(55158089494519/100000000000000 : ℝ), (43165904778753/100000000000000 : ℝ), (1676005706131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6262281451/10000000000 : ℝ)|^75 ≤ (55158089494519/100000000000000 : ℝ)^59
        have hw : |(6262281451/10000000000 : ℝ)|=(6262281451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2581947883/5000000000 : ℝ)|^75 ≤ (43165904778753/100000000000000 : ℝ)^59
        have hw : |(2581947883/5000000000 : ℝ)|=(2581947883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100239001/2500000000 : ℝ)|^75 ≤ (1676005706131/100000000000000 : ℝ)^59
        have hw : |(-100239001/2500000000 : ℝ)|=(100239001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8942932203/10000000000 : ℝ)*x 0 + (429480957/2500000000 : ℝ)*x 1 + (563756781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8942932203/10000000000 : ℝ)^75 ≤ (1735209637779/2000000000000 : ℝ)^59 := by
    have hnat : (8942932203 : ℕ)^75*2000000000000^59 ≤ 1735209637779^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8942932203 10000000000 1735209637779 2000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429480957/2500000000 : ℝ)^75 ≤ (10654849874737/100000000000000 : ℝ)^59 := by
    have hnat : (429480957 : ℕ)^75*100000000000000^59 ≤ 10654849874737^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429480957 2500000000 10654849874737 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563756781/10000000000 : ℝ)^75 ≤ (516933644591/20000000000000 : ℝ)^59 := by
    have hnat : (563756781 : ℕ)^75*20000000000000^59 ≤ 516933644591^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563756781 10000000000 516933644591 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8942932203/10000000000 : ℝ), (429480957/2500000000 : ℝ), (563756781/10000000000 : ℝ)] ![(1735209637779/2000000000000 : ℝ), (10654849874737/100000000000000 : ℝ), (516933644591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8942932203/10000000000 : ℝ)|^75 ≤ (1735209637779/2000000000000 : ℝ)^59
        have hw : |(8942932203/10000000000 : ℝ)|=(8942932203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(429480957/2500000000 : ℝ)|^75 ≤ (10654849874737/100000000000000 : ℝ)^59
        have hw : |(429480957/2500000000 : ℝ)|=(429480957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563756781/10000000000 : ℝ)|^75 ≤ (516933644591/20000000000000 : ℝ)^59
        have hw : |(563756781/10000000000 : ℝ)|=(563756781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-102033671/1000000000 : ℝ)*x 0 + (1324662711/2000000000 : ℝ)*x 1 + (881103363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102033671/1000000000 : ℝ)^75 ≤ (1098900039603/20000000000000 : ℝ)^59 := by
    have hnat : (102033671 : ℕ)^75*20000000000000^59 ≤ 1098900039603^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102033671 1000000000 1098900039603 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324662711/2000000000 : ℝ)^75 ≤ (29615793382189/50000000000000 : ℝ)^59 := by
    have hnat : (1324662711 : ℕ)^75*50000000000000^59 ≤ 29615793382189^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324662711 2000000000 29615793382189 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (881103363/2000000000 : ℝ)^75 ≤ (8818478254771/25000000000000 : ℝ)^59 := by
    have hnat : (881103363 : ℕ)^75*25000000000000^59 ≤ 8818478254771^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881103363 2000000000 8818478254771 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102033671/1000000000 : ℝ), (1324662711/2000000000 : ℝ), (881103363/2000000000 : ℝ)] ![(1098900039603/20000000000000 : ℝ), (29615793382189/50000000000000 : ℝ), (8818478254771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102033671/1000000000 : ℝ)|^75 ≤ (1098900039603/20000000000000 : ℝ)^59
        have hw : |(-102033671/1000000000 : ℝ)|=(102033671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1324662711/2000000000 : ℝ)|^75 ≤ (29615793382189/50000000000000 : ℝ)^59
        have hw : |(1324662711/2000000000 : ℝ)|=(1324662711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(881103363/2000000000 : ℝ)|^75 ≤ (8818478254771/25000000000000 : ℝ)^59
        have hw : |(881103363/2000000000 : ℝ)|=(881103363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1561831679/2500000000 : ℝ)*x 0 + (-10065971/312500000 : ℝ)*x 1 + (1043578459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1561831679/2500000000 : ℝ)^75 ≤ (10998140333261/20000000000000 : ℝ)^59 := by
    have hnat : (1561831679 : ℕ)^75*20000000000000^59 ≤ 10998140333261^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561831679 2500000000 10998140333261 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10065971/312500000 : ℝ)^75 ≤ (1268811238509/100000000000000 : ℝ)^59 := by
    have hnat : (10065971 : ℕ)^75*100000000000000^59 ≤ 1268811238509^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10065971 312500000 1268811238509 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043578459/2000000000 : ℝ)^75 ≤ (43740487079433/100000000000000 : ℝ)^59 := by
    have hnat : (1043578459 : ℕ)^75*100000000000000^59 ≤ 43740487079433^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043578459 2000000000 43740487079433 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1561831679/2500000000 : ℝ), (-10065971/312500000 : ℝ), (1043578459/2000000000 : ℝ)] ![(10998140333261/20000000000000 : ℝ), (1268811238509/100000000000000 : ℝ), (43740487079433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1561831679/2500000000 : ℝ)|^75 ≤ (10998140333261/20000000000000 : ℝ)^59
        have hw : |(1561831679/2500000000 : ℝ)|=(1561831679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10065971/312500000 : ℝ)|^75 ≤ (1268811238509/100000000000000 : ℝ)^59
        have hw : |(-10065971/312500000 : ℝ)|=(10065971/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043578459/2000000000 : ℝ)|^75 ≤ (43740487079433/100000000000000 : ℝ)^59
        have hw : |(1043578459/2000000000 : ℝ)|=(1043578459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (608821511/2500000000 : ℝ)*x 0 + (8221241477/10000000000 : ℝ)*x 1 + (-202392719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (608821511/2500000000 : ℝ)^75 ≤ (16603156152771/100000000000000 : ℝ)^59 := by
    have hnat : (608821511 : ℕ)^75*100000000000000^59 ≤ 16603156152771^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608821511 2500000000 16603156152771 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8221241477/10000000000 : ℝ)^75 ≤ (77959596412317/100000000000000 : ℝ)^59 := by
    have hnat : (8221241477 : ℕ)^75*100000000000000^59 ≤ 77959596412317^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8221241477 10000000000 77959596412317 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202392719/2000000000 : ℝ)^75 ≤ (2718623713661/50000000000000 : ℝ)^59 := by
    have hnat : (202392719 : ℕ)^75*50000000000000^59 ≤ 2718623713661^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202392719 2000000000 2718623713661 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(608821511/2500000000 : ℝ), (8221241477/10000000000 : ℝ), (-202392719/2000000000 : ℝ)] ![(16603156152771/100000000000000 : ℝ), (77959596412317/100000000000000 : ℝ), (2718623713661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(608821511/2500000000 : ℝ)|^75 ≤ (16603156152771/100000000000000 : ℝ)^59
        have hw : |(608821511/2500000000 : ℝ)|=(608821511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8221241477/10000000000 : ℝ)|^75 ≤ (77959596412317/100000000000000 : ℝ)^59
        have hw : |(8221241477/10000000000 : ℝ)|=(8221241477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202392719/2000000000 : ℝ)|^75 ≤ (2718623713661/50000000000000 : ℝ)^59
        have hw : |(-202392719/2000000000 : ℝ)|=(202392719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4534015227/5000000000 : ℝ)*x 0 + (1165791997/10000000000 : ℝ)*x 1 + (194969663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4534015227/5000000000 : ℝ)^75 ≤ (88306172951437/100000000000000 : ℝ)^59 := by
    have hnat : (4534015227 : ℕ)^75*100000000000000^59 ≤ 88306172951437^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534015227 5000000000 88306172951437 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165791997/10000000000 : ℝ)^75 ≤ (6508806486149/100000000000000 : ℝ)^59 := by
    have hnat : (1165791997 : ℕ)^75*100000000000000^59 ≤ 6508806486149^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165791997 10000000000 6508806486149 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194969663/2000000000 : ℝ)^75 ≤ (2592510271421/50000000000000 : ℝ)^59 := by
    have hnat : (194969663 : ℕ)^75*50000000000000^59 ≤ 2592510271421^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194969663 2000000000 2592510271421 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4534015227/5000000000 : ℝ), (1165791997/10000000000 : ℝ), (194969663/2000000000 : ℝ)] ![(88306172951437/100000000000000 : ℝ), (6508806486149/100000000000000 : ℝ), (2592510271421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4534015227/5000000000 : ℝ)|^75 ≤ (88306172951437/100000000000000 : ℝ)^59
        have hw : |(4534015227/5000000000 : ℝ)|=(4534015227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165791997/10000000000 : ℝ)|^75 ≤ (6508806486149/100000000000000 : ℝ)^59
        have hw : |(1165791997/10000000000 : ℝ)|=(1165791997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194969663/2000000000 : ℝ)|^75 ≤ (2592510271421/50000000000000 : ℝ)^59
        have hw : |(194969663/2000000000 : ℝ)|=(194969663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314053_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((81081/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(81081/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40721/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40721/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80333/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80333/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14371/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14371/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31153/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6069/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6069/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (81081/100000 : ℝ) ^ (37/8 : ℝ) ≤ (18954870645180287899/50000000000000000000 : ℝ) := by
    have hpowers : (81081/100000 : ℝ)^37 ≤ (18954870645180287899/50000000000000000000 : ℝ)^8 := by
      have hnat : (81081 : ℕ)^37*50000000000000000000^8 ≤ 18954870645180287899^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81081 100000 18954870645180287899 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81081/100000 : ℝ)) (X := (18954870645180287899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (68954870645180287899/50000000000000000000 : ℝ) ≤ (5359850729631341/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (68954870645180287899/50000000000000000000 : ℝ)^8 ≤ (5359850729631341/5000000000000000 : ℝ)^37 := by
      have hnat : (68954870645180287899 : ℕ)^8*5000000000000000^37 ≤ 5359850729631341^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68954870645180287899 50000000000000000000 5359850729631341 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5359850729631341/5000000000000000 : ℝ)) (X := (68954870645180287899/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (43954870645180287899/25000000000000000000 : ℝ) ≤ (2259526580417633/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (43954870645180287899/25000000000000000000 : ℝ)^8 ≤ (2259526580417633/2000000000000000 : ℝ)^37 := by
      have hnat : (43954870645180287899 : ℕ)^8*2000000000000000^37 ≤ 2259526580417633^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43954870645180287899 25000000000000000000 2259526580417633 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2259526580417633/2000000000000000 : ℝ)) (X := (43954870645180287899/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(9226941785419/103950000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(64214604758387/900900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (81081/100000 : ℝ)) (alpha := (9226941785419/103950000000000 : ℝ)) (beta := (64214604758387/900900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (81081/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(9226941785419/103950000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(64214604758387/900900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (40721/50000 : ℝ) ^ (37/8 : ℝ) ≤ (9674176321267653631/25000000000000000000 : ℝ) := by
    have hpowers : (40721/50000 : ℝ)^37 ≤ (9674176321267653631/25000000000000000000 : ℝ)^8 := by
      have hnat : (40721 : ℕ)^37*25000000000000000000^8 ≤ 9674176321267653631^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40721 50000 9674176321267653631 25000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40721/50000 : ℝ)) (X := (9674176321267653631/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (34674176321267653631/25000000000000000000 : ℝ) ≤ (10732898053716221/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (34674176321267653631/25000000000000000000 : ℝ)^8 ≤ (10732898053716221/10000000000000000 : ℝ)^37 := by
      have hnat : (34674176321267653631 : ℕ)^8*10000000000000000^37 ≤ 10732898053716221^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34674176321267653631 25000000000000000000 10732898053716221 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10732898053716221/10000000000000000 : ℝ)) (X := (34674176321267653631/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (22174176321267653631/12500000000000000000 : ℝ) ≤ (707463988361193/625000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (22174176321267653631/12500000000000000000 : ℝ)^8 ≤ (707463988361193/625000000000000 : ℝ)^37 := by
      have hnat : (22174176321267653631 : ℕ)^8*625000000000000^37 ≤ 707463988361193^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22174176321267653631 12500000000000000000 707463988361193 625000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (707463988361193/625000000000000 : ℝ)) (X := (22174176321267653631/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(732898053716221/8144200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(586525760062867/8144200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (40721/50000 : ℝ)) (alpha := (732898053716221/8144200000000000 : ℝ)) (beta := (586525760062867/8144200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (40721/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(732898053716221/8144200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(586525760062867/8144200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (80333/100000 : ℝ) ^ (37/8 : ℝ) ≤ (36319067076600750333/100000000000000000000 : ℝ) := by
    have hpowers : (80333/100000 : ℝ)^37 ≤ (36319067076600750333/100000000000000000000 : ℝ)^8 := by
      have hnat : (80333 : ℕ)^37*100000000000000000000^8 ≤ 36319067076600750333^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80333 100000 36319067076600750333 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80333/100000 : ℝ)) (X := (36319067076600750333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (136319067076600750333/100000000000000000000 : ℝ) ≤ (5346423098036379/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (136319067076600750333/100000000000000000000 : ℝ)^8 ≤ (5346423098036379/5000000000000000 : ℝ)^37 := by
      have hnat : (136319067076600750333 : ℕ)^8*5000000000000000^37 ≤ 5346423098036379^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136319067076600750333 100000000000000000000 5346423098036379 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5346423098036379/5000000000000000 : ℝ)) (X := (136319067076600750333/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (86319067076600750333/50000000000000000000 : ℝ) ≤ (11253116299206949/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (86319067076600750333/50000000000000000000 : ℝ)^8 ≤ (11253116299206949/10000000000000000 : ℝ)^37 := by
      have hnat : (86319067076600750333 : ℕ)^8*10000000000000000^37 ≤ 11253116299206949^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86319067076600750333 50000000000000000000 11253116299206949 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11253116299206949/10000000000000000 : ℝ)) (X := (86319067076600750333/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(346423098036379/4016650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(560270103134191/8033300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (80333/100000 : ℝ)) (alpha := (346423098036379/4016650000000000 : ℝ)) (beta := (560270103134191/8033300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (80333/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(346423098036379/4016650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(560270103134191/8033300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-436436743/2500000000 : ℝ)*X 0 0+(1039827337/2000000000 : ℝ)*X 0 1+(5390182973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((904271757/2000000000 : ℝ)*X 1 0+(-134552333/1250000000 : ℝ)*X 1 1+(3242408689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((90942783/200000000 : ℝ)*X 2 0+(6504420027/10000000000 : ℝ)*X 2 1+(-1005788911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((7394263907/10000000000 : ℝ)*X 0 0+(1241429871/5000000000 : ℝ)*X 0 1+(2230975029/10000000000 : ℝ)*X 0 2+(7394263907/10000000000 : ℝ)*X 1 0+(1241429871/5000000000 : ℝ)*X 1 1+(2230975029/10000000000 : ℝ)*X 1 2+(7394263907/10000000000 : ℝ)*X 2 0+(1241429871/5000000000 : ℝ)*X 2 1+(2230975029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1816602491/10000000000 : ℝ)*X 0 0+(3815996601/10000000000 : ℝ)*X 0 1+(827289981/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((43820477/125000000 : ℝ)*X 1 0+(-497555099/10000000000 : ℝ)*X 1 1+(95913293/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1766596339/5000000000 : ℝ)*X 2 0+(310873207/400000000 : ℝ)*X 2 1+(-217626527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((96634017/156250000 : ℝ)*X 0 0+(1308797397/2500000000 : ℝ)*X 0 1+(210718233/5000000000 : ℝ)*X 0 2+(96634017/156250000 : ℝ)*X 1 0+(1308797397/2500000000 : ℝ)*X 1 1+(210718233/5000000000 : ℝ)*X 1 2+(96634017/156250000 : ℝ)*X 2 0+(1308797397/2500000000 : ℝ)*X 2 1+(210718233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-531776457/5000000000 : ℝ)*X 0 0+(973274911/2500000000 : ℝ)*X 0 1+(7044886147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2442385733/10000000000 : ℝ)*X 1 0+(-210254939/2000000000 : ℝ)*X 1 1+(2048433087/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6262281451/10000000000 : ℝ)*X 2 0+(2581947883/5000000000 : ℝ)*X 2 1+(-100239001/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8942932203/10000000000 : ℝ)*X 0 0+(429480957/2500000000 : ℝ)*X 0 1+(563756781/10000000000 : ℝ)*X 0 2+(8942932203/10000000000 : ℝ)*X 1 0+(429480957/2500000000 : ℝ)*X 1 1+(563756781/10000000000 : ℝ)*X 1 2+(8942932203/10000000000 : ℝ)*X 2 0+(429480957/2500000000 : ℝ)*X 2 1+(563756781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-102033671/1000000000 : ℝ)*X 0 0+(1324662711/2000000000 : ℝ)*X 0 1+(881103363/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1561831679/2500000000 : ℝ)*X 1 0+(-10065971/312500000 : ℝ)*X 1 1+(1043578459/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((608821511/2500000000 : ℝ)*X 2 0+(8221241477/10000000000 : ℝ)*X 2 1+(-202392719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4534015227/5000000000 : ℝ)*X 0 0+(1165791997/10000000000 : ℝ)*X 0 1+(194969663/2000000000 : ℝ)*X 0 2+(4534015227/5000000000 : ℝ)*X 1 0+(1165791997/10000000000 : ℝ)*X 1 1+(194969663/2000000000 : ℝ)*X 1 2+(4534015227/5000000000 : ℝ)*X 2 0+(1165791997/10000000000 : ℝ)*X 2 1+(194969663/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((14371/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14371/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47863507297684844269630785091/3721035605787500000000000000000000 : ℝ) := by norm_num
    linear_combination (316282557149/1000000000000 : ℝ)*(base7) + (916881/1000000000000 : ℝ)*(base23) + (57853/500000000000 : ℝ)*(base49) + (165199253111/1000000000000 : ℝ)*(base59) + (3075004805421/1000000000000 : ℝ)*(major_s1_0) + (3075004805421/1000000000000 : ℝ)*(major_s1_1) + (3075004805421/1000000000000 : ℝ)*(major_s1_2) + (2717483/125000000000 : ℝ)*(sp_s1_0) + (165577/250000000000 : ℝ)*(sp_s1_6) + (522196503219/125000000000 : ℝ)*(sp_s1_7) + (1044414185991/250000000000 : ℝ)*(sp_s1_8) + (4177655827083/1000000000000 : ℝ)*(sp_s1_9) + (262919809717/125000000000 : ℝ)*(sp_s1_13) + (15744587/250000000000 : ℝ)*(sp_s1_14) + (357415316579/200000000000 : ℝ)*(f.failure) + (1044414185991/250000000000 : ℝ)*(f.sum) + (285991054945448554511/654248018600000000000000000000000 : ℝ)*base62 + (3170467219992051/8033300000000000000000000000 : ℝ)*base64 + (3801404744511447/8144200000000000000000000000 : ℝ)*base66 + (3553923112635501/4016650000000000000000000000 : ℝ)*base68 + (10271599247456797/101219580000000000000000000000 : ℝ)*base71 + (180976447556731/300300000000000000000000000 : ℝ)*base72 + (6358874773465119/8144200000000000000000000000 : ℝ)*base74 + (1766536538147/2165625000000000000000000 : ℝ)*base76 + (1729607314136315863/24457032600000000000000000000000 : ℝ)*base78 + (11951/20000000000000000 : ℝ)*base87 + (11951/20000000000000000 : ℝ)*base89 + (11951/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31153/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1211169412612773315702998863/81931059210000000000000000000000 : ℝ) := by norm_num
    linear_combination (309732540533/500000000000 : ℝ)*(base7) + (366199/500000000000 : ℝ)*(base53) + (722779/1000000000000 : ℝ)*(base59) + (132217707221/62500000000 : ℝ)*(major_s1_0) + (132217707221/62500000000 : ℝ)*(major_s1_1) + (2115482583137/1000000000000 : ℝ)*(major_s1_2) + (35813623/1000000000000 : ℝ)*(sp_s1_0) + (33266531/1000000000000 : ℝ)*(sp_s1_2) + (61235853/500000000000 : ℝ)*(sp_s1_8) + (2638615947231/1000000000000 : ℝ)*(sp_s1_14) + (659632322287/250000000000 : ℝ)*(sp_s1_15) + (2638619226721/1000000000000 : ℝ)*(sp_s1_16) + (184882790231/100000000000 : ℝ)*(sp_s1_20) + (76133789/1000000000000 : ℝ)*(sp_s1_27) + (1229438955033/1000000000000 : ℝ)*(f.failure) + (659663123313/250000000000 : ℝ)*(f.sum) + (13711132438929261/27283070000000000000000000000 : ℝ)*base62 + (1013756319873/6700000000000000000000000 : ℝ)*base64 + (679150224010933/2036050000000000000000000000 : ℝ)*base66 + (369709237823/3350000000000000000000000 : ℝ)*base68 + (7342471195701821/13929300000000000000000000000 : ℝ)*base70 + (134676105855289/450450000000000000000000000 : ℝ)*base72 + (273696670182379/2036050000000000000000000000 : ℝ)*base75 + (6708587197483/12993750000000000000000000 : ℝ)*base77 + (465555775664167/8956432836914062500000000000 : ℝ)*base78 + (26723/100000000000000000 : ℝ)*base86 + (26723/100000000000000000 : ℝ)*base88 + (73277/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6069/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6069/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (90047308666435137420661586687/22326213634725000000000000000000000 : ℝ) := by norm_num
    linear_combination (591567166977/1000000000000 : ℝ)*(base7) + (22657/25000000000 : ℝ)*(base11) + (2630581/500000000000 : ℝ)*(base27) + (86422801199/1000000000000 : ℝ)*(base40) + (1811209/1000000000000 : ℝ)*(base43) + (2078738057369/1000000000000 : ℝ)*(major_s1_0) + (25984203077/12500000000 : ℝ)*(major_s1_1) + (2078738057369/1000000000000 : ℝ)*(major_s1_2) + (2443429/1000000000000 : ℝ)*(sp_s1_1) + (29333271/1000000000000 : ℝ)*(sp_s1_9) + (1301429919047/500000000000 : ℝ)*(sp_s1_21) + (1301430056077/500000000000 : ℝ)*(sp_s1_22) + (2602831411103/1000000000000 : ℝ)*(sp_s1_23) + (28119467273/15625000000 : ℝ)*(sp_s1_27) + (151010499957/125000000000 : ℝ)*(f.failure) + (2602862555583/1000000000000 : ℝ)*(f.sum) + (90404075443871267029/163562004650000000000000000000000 : ℝ)*base62 + (3953433266455701/8033300000000000000000000000 : ℝ)*base65 + (8344612096937/203605000000000000000000000 : ℝ)*base67 + (423941311130477/2008325000000000000000000000 : ℝ)*base68 + (155920779952989613/303658740000000000000000000000 : ℝ)*base70 + (683226601619323/900900000000000000000000000 : ℝ)*base73 + (615518540217/1628840000000000000000000 : ℝ)*base74 + (1207743042311/103950000000000000000000000 : ℝ)*base77 + (14521365652096202303/36685548900000000000000000000000 : ℝ)*base79 + (11467/12500000000000000 : ℝ)*base86 + (11467/12500000000000000 : ℝ)*base88 + (11467/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((81081/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(81081/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40721/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40721/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80333/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80333/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14371/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14371/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31153/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6069/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6069/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314053_s1 p hpa hpb X hX hprev0

#print axioms solution
