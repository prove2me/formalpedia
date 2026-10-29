-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:14.63919+00:00
-- url     : https://prove2.me/submissions/04a108eb-b8bf-4b34-9834-42fe87e2fb8c

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
theorem collision_support_c315053_s2_s2_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-572848483/2500000000 : ℝ)*x 0 + (1263861293/2500000000 : ℝ)*x 1 + (507797091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572848483/2500000000 : ℝ)^19 ≤ (15468909345769/100000000000000 : ℝ)^15 := by
    have hnat : (572848483 : ℕ)^19*100000000000000^15 ≤ 15468909345769^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572848483 2500000000 15468909345769 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263861293/2500000000 : ℝ)^19 ≤ (4214653858011/10000000000000 : ℝ)^15 := by
    have hnat : (1263861293 : ℕ)^19*10000000000000^15 ≤ 4214653858011^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263861293 2500000000 4214653858011 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507797091/1000000000 : ℝ)^19 ≤ (5298069006197/12500000000000 : ℝ)^15 := by
    have hnat : (507797091 : ℕ)^19*12500000000000^15 ≤ 5298069006197^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507797091 1000000000 5298069006197 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-572848483/2500000000 : ℝ), (1263861293/2500000000 : ℝ), (507797091/1000000000 : ℝ)] ![(15468909345769/100000000000000 : ℝ), (4214653858011/10000000000000 : ℝ), (5298069006197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-572848483/2500000000 : ℝ)|^19 ≤ (15468909345769/100000000000000 : ℝ)^15
        have hw : |(-572848483/2500000000 : ℝ)|=(572848483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1263861293/2500000000 : ℝ)|^19 ≤ (4214653858011/10000000000000 : ℝ)^15
        have hw : |(1263861293/2500000000 : ℝ)|=(1263861293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507797091/1000000000 : ℝ)|^19 ≤ (5298069006197/12500000000000 : ℝ)^15
        have hw : |(507797091/1000000000 : ℝ)|=(507797091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (896268301/2000000000 : ℝ)*x 0 + (-222026533/1250000000 : ℝ)*x 1 + (1204680863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896268301/2000000000 : ℝ)^19 ≤ (9044617267359/25000000000000 : ℝ)^15 := by
    have hnat : (896268301 : ℕ)^19*25000000000000^15 ≤ 9044617267359^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896268301 2000000000 9044617267359 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222026533/1250000000 : ℝ)^19 ≤ (11203666212003/100000000000000 : ℝ)^15 := by
    have hnat : (222026533 : ℕ)^19*100000000000000^15 ≤ 11203666212003^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222026533 1250000000 11203666212003 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204680863/2000000000 : ℝ)^19 ≤ (3288616544083/6250000000000 : ℝ)^15 := by
    have hnat : (1204680863 : ℕ)^19*6250000000000^15 ≤ 3288616544083^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204680863 2000000000 3288616544083 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(896268301/2000000000 : ℝ), (-222026533/1250000000 : ℝ), (1204680863/2000000000 : ℝ)] ![(9044617267359/25000000000000 : ℝ), (11203666212003/100000000000000 : ℝ), (3288616544083/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(896268301/2000000000 : ℝ)|^19 ≤ (9044617267359/25000000000000 : ℝ)^15
        have hw : |(896268301/2000000000 : ℝ)|=(896268301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222026533/1250000000 : ℝ)|^19 ≤ (11203666212003/100000000000000 : ℝ)^15
        have hw : |(-222026533/1250000000 : ℝ)|=(222026533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204680863/2000000000 : ℝ)|^19 ≤ (3288616544083/6250000000000 : ℝ)^15
        have hw : |(1204680863/2000000000 : ℝ)|=(1204680863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4502410333/10000000000 : ℝ)*x 0 + (6015735373/10000000000 : ℝ)*x 1 + (-1759828237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4502410333/10000000000 : ℝ)^19 ≤ (9098513290071/25000000000000 : ℝ)^15 := by
    have hnat : (4502410333 : ℕ)^19*25000000000000^15 ≤ 9098513290071^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502410333 10000000000 9098513290071 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6015735373/10000000000 : ℝ)^19 ≤ (52533021856089/100000000000000 : ℝ)^15 := by
    have hnat : (6015735373 : ℕ)^19*100000000000000^15 ≤ 52533021856089^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015735373 10000000000 52533021856089 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759828237/10000000000 : ℝ)^19 ≤ (5536462482589/50000000000000 : ℝ)^15 := by
    have hnat : (1759828237 : ℕ)^19*50000000000000^15 ≤ 5536462482589^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759828237 10000000000 5536462482589 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4502410333/10000000000 : ℝ), (6015735373/10000000000 : ℝ), (-1759828237/10000000000 : ℝ)] ![(9098513290071/25000000000000 : ℝ), (52533021856089/100000000000000 : ℝ), (5536462482589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4502410333/10000000000 : ℝ)|^19 ≤ (9098513290071/25000000000000 : ℝ)^15
        have hw : |(4502410333/10000000000 : ℝ)|=(4502410333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6015735373/10000000000 : ℝ)|^19 ≤ (52533021856089/100000000000000 : ℝ)^15
        have hw : |(6015735373/10000000000 : ℝ)|=(6015735373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1759828237/10000000000 : ℝ)|^19 ≤ (5536462482589/50000000000000 : ℝ)^15
        have hw : |(-1759828237/10000000000 : ℝ)|=(1759828237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1345505741/2000000000 : ℝ)*x 0 + (2794623093/10000000000 : ℝ)*x 1 + (1380038343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345505741/2000000000 : ℝ)^19 ≤ (60527170944187/100000000000000 : ℝ)^15 := by
    have hnat : (1345505741 : ℕ)^19*100000000000000^15 ≤ 60527170944187^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345505741 2000000000 60527170944187 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794623093/10000000000 : ℝ)^19 ≤ (19891892721957/100000000000000 : ℝ)^15 := by
    have hnat : (2794623093 : ℕ)^19*100000000000000^15 ≤ 19891892721957^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794623093 10000000000 19891892721957 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380038343/5000000000 : ℝ)^19 ≤ (19580936318129/100000000000000 : ℝ)^15 := by
    have hnat : (1380038343 : ℕ)^19*100000000000000^15 ≤ 19580936318129^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380038343 5000000000 19580936318129 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345505741/2000000000 : ℝ), (2794623093/10000000000 : ℝ), (1380038343/5000000000 : ℝ)] ![(60527170944187/100000000000000 : ℝ), (19891892721957/100000000000000 : ℝ), (19580936318129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345505741/2000000000 : ℝ)|^19 ≤ (60527170944187/100000000000000 : ℝ)^15
        have hw : |(1345505741/2000000000 : ℝ)|=(1345505741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794623093/10000000000 : ℝ)|^19 ≤ (19891892721957/100000000000000 : ℝ)^15
        have hw : |(2794623093/10000000000 : ℝ)|=(2794623093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380038343/5000000000 : ℝ)|^19 ≤ (19580936318129/100000000000000 : ℝ)^15
        have hw : |(1380038343/5000000000 : ℝ)|=(1380038343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-224955127/1000000000 : ℝ)*x 0 + (870774423/2000000000 : ℝ)*x 1 + (2893144057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224955127/1000000000 : ℝ)^19 ≤ (7555991700793/50000000000000 : ℝ)^15 := by
    have hnat : (224955127 : ℕ)^19*50000000000000^15 ≤ 7555991700793^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224955127 1000000000 7555991700793 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (870774423/2000000000 : ℝ)^19 ≤ (17439974720813/50000000000000 : ℝ)^15 := by
    have hnat : (870774423 : ℕ)^19*50000000000000^15 ≤ 17439974720813^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870774423 2000000000 17439974720813 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2893144057/5000000000 : ℝ)^19 ≤ (50008067143749/100000000000000 : ℝ)^15 := by
    have hnat : (2893144057 : ℕ)^19*100000000000000^15 ≤ 50008067143749^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893144057 5000000000 50008067143749 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224955127/1000000000 : ℝ), (870774423/2000000000 : ℝ), (2893144057/5000000000 : ℝ)] ![(7555991700793/50000000000000 : ℝ), (17439974720813/50000000000000 : ℝ), (50008067143749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224955127/1000000000 : ℝ)|^19 ≤ (7555991700793/50000000000000 : ℝ)^15
        have hw : |(-224955127/1000000000 : ℝ)|=(224955127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(870774423/2000000000 : ℝ)|^19 ≤ (17439974720813/50000000000000 : ℝ)^15
        have hw : |(870774423/2000000000 : ℝ)|=(870774423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2893144057/5000000000 : ℝ)|^19 ≤ (50008067143749/100000000000000 : ℝ)^15
        have hw : |(2893144057/5000000000 : ℝ)|=(2893144057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2143671241/5000000000 : ℝ)*x 0 + (-302636171/2000000000 : ℝ)*x 1 + (6384825391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143671241/5000000000 : ℝ)^19 ≤ (34206215268951/100000000000000 : ℝ)^15 := by
    have hnat : (2143671241 : ℕ)^19*100000000000000^15 ≤ 34206215268951^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143671241 5000000000 34206215268951 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302636171/2000000000 : ℝ)^19 ≤ (9145239033677/100000000000000 : ℝ)^15 := by
    have hnat : (302636171 : ℕ)^19*100000000000000^15 ≤ 9145239033677^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302636171 2000000000 9145239033677 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6384825391/10000000000 : ℝ)^19 ≤ (56648545683521/100000000000000 : ℝ)^15 := by
    have hnat : (6384825391 : ℕ)^19*100000000000000^15 ≤ 56648545683521^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6384825391 10000000000 56648545683521 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143671241/5000000000 : ℝ), (-302636171/2000000000 : ℝ), (6384825391/10000000000 : ℝ)] ![(34206215268951/100000000000000 : ℝ), (9145239033677/100000000000000 : ℝ), (56648545683521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143671241/5000000000 : ℝ)|^19 ≤ (34206215268951/100000000000000 : ℝ)^15
        have hw : |(2143671241/5000000000 : ℝ)|=(2143671241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-302636171/2000000000 : ℝ)|^19 ≤ (9145239033677/100000000000000 : ℝ)^15
        have hw : |(-302636171/2000000000 : ℝ)|=(302636171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6384825391/10000000000 : ℝ)|^19 ≤ (56648545683521/100000000000000 : ℝ)^15
        have hw : |(6384825391/10000000000 : ℝ)|=(6384825391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (107712031/250000000 : ℝ)*x 0 + (6650853681/10000000000 : ℝ)*x 1 + (-537103273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107712031/250000000 : ℝ)^19 ≤ (17209991888093/50000000000000 : ℝ)^15 := by
    have hnat : (107712031 : ℕ)^19*50000000000000^15 ≤ 17209991888093^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107712031 250000000 17209991888093 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6650853681/10000000000 : ℝ)^19 ≤ (29827352222471/50000000000000 : ℝ)^15 := by
    have hnat : (6650853681 : ℕ)^19*50000000000000^15 ≤ 29827352222471^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6650853681 10000000000 29827352222471 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537103273/5000000000 : ℝ)^19 ≤ (92582996413/1562500000000 : ℝ)^15 := by
    have hnat : (537103273 : ℕ)^19*1562500000000^15 ≤ 92582996413^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537103273 5000000000 92582996413 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107712031/250000000 : ℝ), (6650853681/10000000000 : ℝ), (-537103273/5000000000 : ℝ)] ![(17209991888093/50000000000000 : ℝ), (29827352222471/50000000000000 : ℝ), (92582996413/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107712031/250000000 : ℝ)|^19 ≤ (17209991888093/50000000000000 : ℝ)^15
        have hw : |(107712031/250000000 : ℝ)|=(107712031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6650853681/10000000000 : ℝ)|^19 ≤ (29827352222471/50000000000000 : ℝ)^15
        have hw : |(6650853681/10000000000 : ℝ)|=(6650853681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537103273/5000000000 : ℝ)|^19 ≤ (92582996413/1562500000000 : ℝ)^15
        have hw : |(-537103273/5000000000 : ℝ)|=(537103273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (165106159/250000000 : ℝ)*x 0 + (186120283/500000000 : ℝ)*x 1 + (238604107/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165106159/250000000 : ℝ)^19 ≤ (29562839165109/50000000000000 : ℝ)^15 := by
    have hnat : (165106159 : ℕ)^19*50000000000000^15 ≤ 29562839165109^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165106159 250000000 29562839165109 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186120283/500000000 : ℝ)^19 ≤ (28600701575961/100000000000000 : ℝ)^15 := by
    have hnat : (186120283 : ℕ)^19*100000000000000^15 ≤ 28600701575961^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186120283 500000000 28600701575961 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238604107/1250000000 : ℝ)^19 ≤ (2454724013783/20000000000000 : ℝ)^15 := by
    have hnat : (238604107 : ℕ)^19*20000000000000^15 ≤ 2454724013783^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238604107 1250000000 2454724013783 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165106159/250000000 : ℝ), (186120283/500000000 : ℝ), (238604107/1250000000 : ℝ)] ![(29562839165109/50000000000000 : ℝ), (28600701575961/100000000000000 : ℝ), (2454724013783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165106159/250000000 : ℝ)|^19 ≤ (29562839165109/50000000000000 : ℝ)^15
        have hw : |(165106159/250000000 : ℝ)|=(165106159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186120283/500000000 : ℝ)|^19 ≤ (28600701575961/100000000000000 : ℝ)^15
        have hw : |(186120283/500000000 : ℝ)|=(186120283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238604107/1250000000 : ℝ)|^19 ≤ (2454724013783/20000000000000 : ℝ)^15
        have hw : |(238604107/1250000000 : ℝ)|=(238604107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-401062843/2500000000 : ℝ)*x 0 + (4934678811/10000000000 : ℝ)*x 1 + (1143875893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401062843/2500000000 : ℝ)^19 ≤ (246198313279/2500000000000 : ℝ)^15 := by
    have hnat : (401062843 : ℕ)^19*2500000000000^15 ≤ 246198313279^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401062843 2500000000 246198313279 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4934678811/10000000000 : ℝ)^19 ≤ (20437664502553/50000000000000 : ℝ)^15 := by
    have hnat : (4934678811 : ℕ)^19*50000000000000^15 ≤ 20437664502553^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934678811 10000000000 20437664502553 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143875893/2000000000 : ℝ)^19 ≤ (49276738453731/100000000000000 : ℝ)^15 := by
    have hnat : (1143875893 : ℕ)^19*100000000000000^15 ≤ 49276738453731^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143875893 2000000000 49276738453731 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401062843/2500000000 : ℝ), (4934678811/10000000000 : ℝ), (1143875893/2000000000 : ℝ)] ![(246198313279/2500000000000 : ℝ), (20437664502553/50000000000000 : ℝ), (49276738453731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401062843/2500000000 : ℝ)|^19 ≤ (246198313279/2500000000000 : ℝ)^15
        have hw : |(-401062843/2500000000 : ℝ)|=(401062843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4934678811/10000000000 : ℝ)|^19 ≤ (20437664502553/50000000000000 : ℝ)^15
        have hw : |(4934678811/10000000000 : ℝ)|=(4934678811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143875893/2000000000 : ℝ)|^19 ≤ (49276738453731/100000000000000 : ℝ)^15
        have hw : |(1143875893/2000000000 : ℝ)|=(1143875893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4182798451/10000000000 : ℝ)*x 0 + (-160255089/1000000000 : ℝ)*x 1 + (6417156501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182798451/10000000000 : ℝ)^19 ≤ (33153149252313/100000000000000 : ℝ)^15 := by
    have hnat : (4182798451 : ℕ)^19*100000000000000^15 ≤ 33153149252313^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182798451 10000000000 33153149252313 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160255089/1000000000 : ℝ)^19 ≤ (9834712099771/100000000000000 : ℝ)^15 := by
    have hnat : (160255089 : ℕ)^19*100000000000000^15 ≤ 9834712099771^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160255089 1000000000 9834712099771 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6417156501/10000000000 : ℝ)^19 ≤ (28506069318083/50000000000000 : ℝ)^15 := by
    have hnat : (6417156501 : ℕ)^19*50000000000000^15 ≤ 28506069318083^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6417156501 10000000000 28506069318083 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182798451/10000000000 : ℝ), (-160255089/1000000000 : ℝ), (6417156501/10000000000 : ℝ)] ![(33153149252313/100000000000000 : ℝ), (9834712099771/100000000000000 : ℝ), (28506069318083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182798451/10000000000 : ℝ)|^19 ≤ (33153149252313/100000000000000 : ℝ)^15
        have hw : |(4182798451/10000000000 : ℝ)|=(4182798451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-160255089/1000000000 : ℝ)|^19 ≤ (9834712099771/100000000000000 : ℝ)^15
        have hw : |(-160255089/1000000000 : ℝ)|=(160255089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6417156501/10000000000 : ℝ)|^19 ≤ (28506069318083/50000000000000 : ℝ)^15
        have hw : |(6417156501/10000000000 : ℝ)|=(6417156501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1042420259/2000000000 : ℝ)*x 0 + (144172129/250000000 : ℝ)*x 1 + (-1141116433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042420259/2000000000 : ℝ)^19 ≤ (43807614704327/100000000000000 : ℝ)^15 := by
    have hnat : (1042420259 : ℕ)^19*100000000000000^15 ≤ 43807614704327^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042420259 2000000000 43807614704327 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144172129/250000000 : ℝ)^19 ≤ (49795754512003/100000000000000 : ℝ)^15 := by
    have hnat : (144172129 : ℕ)^19*100000000000000^15 ≤ 49795754512003^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144172129 250000000 49795754512003 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141116433/10000000000 : ℝ)^19 ≤ (255865230401/4000000000000 : ℝ)^15 := by
    have hnat : (1141116433 : ℕ)^19*4000000000000^15 ≤ 255865230401^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141116433 10000000000 255865230401 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042420259/2000000000 : ℝ), (144172129/250000000 : ℝ), (-1141116433/10000000000 : ℝ)] ![(43807614704327/100000000000000 : ℝ), (49795754512003/100000000000000 : ℝ), (255865230401/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042420259/2000000000 : ℝ)|^19 ≤ (43807614704327/100000000000000 : ℝ)^15
        have hw : |(1042420259/2000000000 : ℝ)|=(1042420259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(144172129/250000000 : ℝ)|^19 ≤ (49795754512003/100000000000000 : ℝ)^15
        have hw : |(144172129/250000000 : ℝ)|=(144172129/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1141116433/10000000000 : ℝ)|^19 ≤ (255865230401/4000000000000 : ℝ)^15
        have hw : |(-1141116433/10000000000 : ℝ)|=(1141116433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1877233541/2500000000 : ℝ)*x 0 + (2674239567/10000000000 : ℝ)*x 1 + (365645087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1877233541/2500000000 : ℝ)^19 ≤ (69566343310347/100000000000000 : ℝ)^15 := by
    have hnat : (1877233541 : ℕ)^19*100000000000000^15 ≤ 69566343310347^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877233541 2500000000 69566343310347 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2674239567/10000000000 : ℝ)^19 ≤ (18812812462791/100000000000000 : ℝ)^15 := by
    have hnat : (2674239567 : ℕ)^19*100000000000000^15 ≤ 18812812462791^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674239567 10000000000 18812812462791 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365645087/2000000000 : ℝ)^19 ≤ (5810422106989/50000000000000 : ℝ)^15 := by
    have hnat : (365645087 : ℕ)^19*50000000000000^15 ≤ 5810422106989^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365645087 2000000000 5810422106989 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1877233541/2500000000 : ℝ), (2674239567/10000000000 : ℝ), (365645087/2000000000 : ℝ)] ![(69566343310347/100000000000000 : ℝ), (18812812462791/100000000000000 : ℝ), (5810422106989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1877233541/2500000000 : ℝ)|^19 ≤ (69566343310347/100000000000000 : ℝ)^15
        have hw : |(1877233541/2500000000 : ℝ)|=(1877233541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2674239567/10000000000 : ℝ)|^19 ≤ (18812812462791/100000000000000 : ℝ)^15
        have hw : |(2674239567/10000000000 : ℝ)|=(2674239567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(365645087/2000000000 : ℝ)|^19 ≤ (5810422106989/50000000000000 : ℝ)^15
        have hw : |(365645087/2000000000 : ℝ)|=(365645087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-763693889/5000000000 : ℝ)*x 0 + (1338038449/2500000000 : ℝ)*x 1 + (5365014711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (763693889/5000000000 : ℝ)^19 ≤ (4627067109321/50000000000000 : ℝ)^15 := by
    have hnat : (763693889 : ℕ)^19*50000000000000^15 ≤ 4627067109321^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763693889 5000000000 4627067109321 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338038449/2500000000 : ℝ)^19 ≤ (2265198218633/5000000000000 : ℝ)^15 := by
    have hnat : (1338038449 : ℕ)^19*5000000000000^15 ≤ 2265198218633^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338038449 2500000000 2265198218633 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5365014711/10000000000 : ℝ)^19 ≤ (45441901403399/100000000000000 : ℝ)^15 := by
    have hnat : (5365014711 : ℕ)^19*100000000000000^15 ≤ 45441901403399^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365014711 10000000000 45441901403399 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-763693889/5000000000 : ℝ), (1338038449/2500000000 : ℝ), (5365014711/10000000000 : ℝ)] ![(4627067109321/50000000000000 : ℝ), (2265198218633/5000000000000 : ℝ), (45441901403399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-763693889/5000000000 : ℝ)|^19 ≤ (4627067109321/50000000000000 : ℝ)^15
        have hw : |(-763693889/5000000000 : ℝ)|=(763693889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1338038449/2500000000 : ℝ)|^19 ≤ (2265198218633/5000000000000 : ℝ)^15
        have hw : |(1338038449/2500000000 : ℝ)|=(1338038449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5365014711/10000000000 : ℝ)|^19 ≤ (45441901403399/100000000000000 : ℝ)^15
        have hw : |(5365014711/10000000000 : ℝ)|=(5365014711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5267827139/10000000000 : ℝ)*x 0 + (-307317969/2500000000 : ℝ)*x 1 + (5654463433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267827139/10000000000 : ℝ)^19 ≤ (44401732848127/100000000000000 : ℝ)^15 := by
    have hnat : (5267827139 : ℕ)^19*100000000000000^15 ≤ 44401732848127^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267827139 10000000000 44401732848127 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307317969/2500000000 : ℝ)^19 ≤ (7028900537559/100000000000000 : ℝ)^15 := by
    have hnat : (307317969 : ℕ)^19*100000000000000^15 ≤ 7028900537559^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307317969 2500000000 7028900537559 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654463433/10000000000 : ℝ)^19 ≤ (48569366601521/100000000000000 : ℝ)^15 := by
    have hnat : (5654463433 : ℕ)^19*100000000000000^15 ≤ 48569366601521^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654463433 10000000000 48569366601521 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267827139/10000000000 : ℝ), (-307317969/2500000000 : ℝ), (5654463433/10000000000 : ℝ)] ![(44401732848127/100000000000000 : ℝ), (7028900537559/100000000000000 : ℝ), (48569366601521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267827139/10000000000 : ℝ)|^19 ≤ (44401732848127/100000000000000 : ℝ)^15
        have hw : |(5267827139/10000000000 : ℝ)|=(5267827139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-307317969/2500000000 : ℝ)|^19 ≤ (7028900537559/100000000000000 : ℝ)^15
        have hw : |(-307317969/2500000000 : ℝ)|=(307317969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5654463433/10000000000 : ℝ)|^19 ≤ (48569366601521/100000000000000 : ℝ)^15
        have hw : |(5654463433/10000000000 : ℝ)|=(5654463433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (33351941/80000000 : ℝ)*x 0 + (409199137/625000000 : ℝ)*x 1 + (-1429051253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33351941/80000000 : ℝ)^19 ≤ (16507302060969/50000000000000 : ℝ)^15 := by
    have hnat : (33351941 : ℕ)^19*50000000000000^15 ≤ 16507302060969^15*80000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33351941 80000000 16507302060969 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409199137/625000000 : ℝ)^19 ≤ (58479359802541/100000000000000 : ℝ)^15 := by
    have hnat : (409199137 : ℕ)^19*100000000000000^15 ≤ 58479359802541^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409199137 625000000 58479359802541 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1429051253/10000000000 : ℝ)^19 ≤ (4253018032393/50000000000000 : ℝ)^15 := by
    have hnat : (1429051253 : ℕ)^19*50000000000000^15 ≤ 4253018032393^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429051253 10000000000 4253018032393 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33351941/80000000 : ℝ), (409199137/625000000 : ℝ), (-1429051253/10000000000 : ℝ)] ![(16507302060969/50000000000000 : ℝ), (58479359802541/100000000000000 : ℝ), (4253018032393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33351941/80000000 : ℝ)|^19 ≤ (16507302060969/50000000000000 : ℝ)^15
        have hw : |(33351941/80000000 : ℝ)|=(33351941/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(409199137/625000000 : ℝ)|^19 ≤ (58479359802541/100000000000000 : ℝ)^15
        have hw : |(409199137/625000000 : ℝ)|=(409199137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1429051253/10000000000 : ℝ)|^19 ≤ (4253018032393/50000000000000 : ℝ)^15
        have hw : |(-1429051253/10000000000 : ℝ)|=(1429051253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s2_s2_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7596057451/10000000000 : ℝ)*x 0 + (2199807163/10000000000 : ℝ)*x 1 + (2203326443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7596057451/10000000000 : ℝ)^19 ≤ (35295156287699/50000000000000 : ℝ)^15 := by
    have hnat : (7596057451 : ℕ)^19*50000000000000^15 ≤ 35295156287699^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7596057451 10000000000 35295156287699 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199807163/10000000000 : ℝ)^19 ≤ (7344978226329/50000000000000 : ℝ)^15 := by
    have hnat : (2199807163 : ℕ)^19*50000000000000^15 ≤ 7344978226329^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199807163 10000000000 7344978226329 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203326443/10000000000 : ℝ)^19 ≤ (14719730964673/100000000000000 : ℝ)^15 := by
    have hnat : (2203326443 : ℕ)^19*100000000000000^15 ≤ 14719730964673^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203326443 10000000000 14719730964673 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7596057451/10000000000 : ℝ), (2199807163/10000000000 : ℝ), (2203326443/10000000000 : ℝ)] ![(35295156287699/50000000000000 : ℝ), (7344978226329/50000000000000 : ℝ), (14719730964673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7596057451/10000000000 : ℝ)|^19 ≤ (35295156287699/50000000000000 : ℝ)^15
        have hw : |(7596057451/10000000000 : ℝ)|=(7596057451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2199807163/10000000000 : ℝ)|^19 ≤ (7344978226329/50000000000000 : ℝ)^15
        have hw : |(2199807163/10000000000 : ℝ)|=(2199807163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203326443/10000000000 : ℝ)|^19 ≤ (14719730964673/100000000000000 : ℝ)^15
        have hw : |(2203326443/10000000000 : ℝ)|=(2203326443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315053_s2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((27017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14819/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14819/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14383/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14383/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13083/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13083/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15727/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15727/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30299/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(30299/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (27017/50000 : ℝ) ^ (75/16 : ℝ) ≤ (279156099842661431/5000000000000000000 : ℝ) := by
    have hpowers : (27017/50000 : ℝ)^75 ≤ (279156099842661431/5000000000000000000 : ℝ)^16 := by
      have hnat : (27017 : ℕ)^75*5000000000000000000^16 ≤ 279156099842661431^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27017 50000 279156099842661431 5000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27017/50000 : ℝ)) (X := (279156099842661431/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (5279156099842661431/5000000000000000000 : ℝ) ≤ (2529143678288547/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (5279156099842661431/5000000000000000000 : ℝ)^16 ≤ (2529143678288547/2500000000000000 : ℝ)^75 := by
      have hnat : (5279156099842661431 : ℕ)^16*2500000000000000^75 ≤ 2529143678288547^75*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5279156099842661431 5000000000000000000 2529143678288547 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529143678288547/2500000000000000 : ℝ)) (X := (5279156099842661431/5000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (2779156099842661431/2500000000000000000 : ℝ) ≤ (1022839659279337/1000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2779156099842661431/2500000000000000000 : ℝ)^16 ≤ (1022839659279337/1000000000000000 : ℝ)^75 := by
      have hnat : (2779156099842661431 : ℕ)^16*1000000000000000^75 ≤ 1022839659279337^75*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2779156099842661431 2500000000000000000 1022839659279337 1000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1022839659279337/1000000000000000 : ℝ)) (X := (2779156099842661431/2500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29143678288547/1350850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(55910939819591/2701700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (27017/50000 : ℝ)) (alpha := (29143678288547/1350850000000000 : ℝ)) (beta := (55910939819591/2701700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (27017/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29143678288547/1350850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(55910939819591/2701700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (14819/25000 : ℝ) ^ (75/16 : ℝ) ≤ (1077158981216077801/12500000000000000000 : ℝ) := by
    have hpowers : (14819/25000 : ℝ)^75 ≤ (1077158981216077801/12500000000000000000 : ℝ)^16 := by
      have hnat : (14819 : ℕ)^75*12500000000000000000^16 ≤ 1077158981216077801^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14819 25000 1077158981216077801 12500000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14819/25000 : ℝ)) (X := (1077158981216077801/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (13577158981216077801/12500000000000000000 : ℝ) ≤ (10177905868793733/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (13577158981216077801/12500000000000000000 : ℝ)^16 ≤ (10177905868793733/10000000000000000 : ℝ)^75 := by
      have hnat : (13577158981216077801 : ℕ)^16*10000000000000000^75 ≤ 10177905868793733^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13577158981216077801 12500000000000000000 10177905868793733 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10177905868793733/10000000000000000 : ℝ)) (X := (13577158981216077801/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (7327158981216077801/6250000000000000000 : ℝ) ≤ (646564533328301/625000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (7327158981216077801/6250000000000000000 : ℝ)^16 ≤ (646564533328301/625000000000000 : ℝ)^75 := by
      have hnat : (7327158981216077801 : ℕ)^16*625000000000000^75 ≤ 646564533328301^75*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7327158981216077801 6250000000000000000 646564533328301 625000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (646564533328301/625000000000000 : ℝ)) (X := (7327158981216077801/6250000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(177905868793733/5927600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(23875237779869/846800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (14819/25000 : ℝ)) (alpha := (177905868793733/5927600000000000 : ℝ)) (beta := (23875237779869/846800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14819/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(177905868793733/5927600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(23875237779869/846800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (14383/25000 : ℝ) ^ (75/16 : ℝ) ≤ (7491618422966834463/100000000000000000000 : ℝ) := by
    have hpowers : (14383/25000 : ℝ)^75 ≤ (7491618422966834463/100000000000000000000 : ℝ)^16 := by
      have hnat : (14383 : ℕ)^75*100000000000000000000^16 ≤ 7491618422966834463^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14383 25000 7491618422966834463 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14383/25000 : ℝ)) (X := (7491618422966834463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (107491618422966834463/100000000000000000000 : ℝ) ≤ (10155311478020317/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (107491618422966834463/100000000000000000000 : ℝ)^16 ≤ (10155311478020317/10000000000000000 : ℝ)^75 := by
      have hnat : (107491618422966834463 : ℕ)^16*10000000000000000^75 ≤ 10155311478020317^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107491618422966834463 100000000000000000000 10155311478020317 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10155311478020317/10000000000000000 : ℝ)) (X := (107491618422966834463/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (57491618422966834463/50000000000000000000 : ℝ) ≤ (10302327853576909/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (57491618422966834463/50000000000000000000 : ℝ)^16 ≤ (10302327853576909/10000000000000000 : ℝ)^75 := by
      have hnat : (57491618422966834463 : ℕ)^16*10000000000000000^75 ≤ 10302327853576909^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57491618422966834463 50000000000000000000 10302327853576909 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10302327853576909/10000000000000000 : ℝ)) (X := (57491618422966834463/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(155311478020317/5753200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9188523472287/359575000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (14383/25000 : ℝ)) (alpha := (155311478020317/5753200000000000 : ℝ)) (beta := (9188523472287/359575000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (14383/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(155311478020317/5753200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9188523472287/359575000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-572848483/2500000000 : ℝ)*X 0 0+(1263861293/2500000000 : ℝ)*X 0 1+(507797091/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((896268301/2000000000 : ℝ)*X 1 0+(-222026533/1250000000 : ℝ)*X 1 1+(1204680863/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4502410333/10000000000 : ℝ)*X 2 0+(6015735373/10000000000 : ℝ)*X 2 1+(-1759828237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1345505741/2000000000 : ℝ)*X 0 0+(2794623093/10000000000 : ℝ)*X 0 1+(1380038343/5000000000 : ℝ)*X 0 2+(1345505741/2000000000 : ℝ)*X 1 0+(2794623093/10000000000 : ℝ)*X 1 1+(1380038343/5000000000 : ℝ)*X 1 2+(1345505741/2000000000 : ℝ)*X 2 0+(2794623093/10000000000 : ℝ)*X 2 1+(1380038343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-224955127/1000000000 : ℝ)*X 0 0+(870774423/2000000000 : ℝ)*X 0 1+(2893144057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2143671241/5000000000 : ℝ)*X 1 0+(-302636171/2000000000 : ℝ)*X 1 1+(6384825391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((107712031/250000000 : ℝ)*X 2 0+(6650853681/10000000000 : ℝ)*X 2 1+(-537103273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((165106159/250000000 : ℝ)*X 0 0+(186120283/500000000 : ℝ)*X 0 1+(238604107/1250000000 : ℝ)*X 0 2+(165106159/250000000 : ℝ)*X 1 0+(186120283/500000000 : ℝ)*X 1 1+(238604107/1250000000 : ℝ)*X 1 2+(165106159/250000000 : ℝ)*X 2 0+(186120283/500000000 : ℝ)*X 2 1+(238604107/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-401062843/2500000000 : ℝ)*X 0 0+(4934678811/10000000000 : ℝ)*X 0 1+(1143875893/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4182798451/10000000000 : ℝ)*X 1 0+(-160255089/1000000000 : ℝ)*X 1 1+(6417156501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1042420259/2000000000 : ℝ)*X 2 0+(144172129/250000000 : ℝ)*X 2 1+(-1141116433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1877233541/2500000000 : ℝ)*X 0 0+(2674239567/10000000000 : ℝ)*X 0 1+(365645087/2000000000 : ℝ)*X 0 2+(1877233541/2500000000 : ℝ)*X 1 0+(2674239567/10000000000 : ℝ)*X 1 1+(365645087/2000000000 : ℝ)*X 1 2+(1877233541/2500000000 : ℝ)*X 2 0+(2674239567/10000000000 : ℝ)*X 2 1+(365645087/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-763693889/5000000000 : ℝ)*X 0 0+(1338038449/2500000000 : ℝ)*X 0 1+(5365014711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5267827139/10000000000 : ℝ)*X 1 0+(-307317969/2500000000 : ℝ)*X 1 1+(5654463433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((33351941/80000000 : ℝ)*X 2 0+(409199137/625000000 : ℝ)*X 2 1+(-1429051253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7596057451/10000000000 : ℝ)*X 0 0+(2199807163/10000000000 : ℝ)*X 0 1+(2203326443/10000000000 : ℝ)*X 0 2+(7596057451/10000000000 : ℝ)*X 1 0+(2199807163/10000000000 : ℝ)*X 1 1+(2203326443/10000000000 : ℝ)*X 1 2+(7596057451/10000000000 : ℝ)*X 2 0+(2199807163/10000000000 : ℝ)*X 2 1+(2203326443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((13083/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13083/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4108388608931078976877583744901/230337947500360000000000000000000000 : ℝ) := by norm_num
    linear_combination (43741/31250000000 : ℝ)*(base8) + (25935766233/100000000000 : ℝ)*(base49) + (992173778709/1000000000000 : ℝ)*(base59) + (283832201939/40000000000 : ℝ)*(major_s2_0) + (283832201939/40000000000 : ℝ)*(major_s2_1) + (283832201939/40000000000 : ℝ)*(major_s2_2) + (34165971/250000000000 : ℝ)*(sp_s2_0) + (4909189/200000000000 : ℝ)*(sp_s2_6) + (5064401979283/500000000000 : ℝ)*(sp_s2_7) + (2532097844581/250000000000 : ℝ)*(sp_s2_8) + (2532133097601/250000000000 : ℝ)*(sp_s2_9) + (406263758339/100000000000 : ℝ)*(sp_s2_13) + (550643837/1000000000000 : ℝ)*(sp_s2_15) + (409631757/1000000000000 : ℝ)*(sp_s2_23) + (812532425867/200000000000 : ℝ)*(f.failure) + (10128942022161/1000000000000 : ℝ)*(f.sum) + (606324393952953941/8525667080000000000000000000000 : ℝ)*base62 + (76962966278939/143830000000000000000000000 : ℝ)*base64 + (172046918747219/169360000000000000000000000 : ℝ)*base66 + (22346707479321/230128000000000000000000000 : ℝ)*base68 + (1039643697495523/9714637775000000000000000000 : ℝ)*base71 + (13073446149709/540340000000000000000000000 : ℝ)*base72 + (23260656875697/237104000000000000000000000 : ℝ)*base74 + (367624521909/67542500000000000000000000 : ℝ)*base76 + (282617886143672227/915119824000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (4353/20000000000000000 : ℝ)*base87 + (4353/20000000000000000 : ℝ)*base89 + (4353/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15727/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15727/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1035463826302470137730270201189/115168973750180000000000000000000000 : ℝ) := by norm_num
    linear_combination (70307/500000000000 : ℝ)*(base39) + (70481157161/200000000000 : ℝ)*(base49) + (398391357/800000000 : ℝ)*(base59) + (3474374845469/500000000000 : ℝ)*(major_s2_0) + (3474374845469/500000000000 : ℝ)*(major_s2_1) + (3474374845469/500000000000 : ℝ)*(major_s2_2) + (9715309/500000000000 : ℝ)*(sp_s2_1) + (1269387/250000000000 : ℝ)*(sp_s2_2) + (50911451/1000000000000 : ℝ)*(sp_s2_7) + (1239872379793/125000000000 : ℝ)*(sp_s2_14) + (9919010519177/1000000000000 : ℝ)*(sp_s2_15) + (9919024872247/1000000000000 : ℝ)*(sp_s2_16) + (1989193782851/500000000000 : ℝ)*(sp_s2_20) + (78869431/1000000000000 : ℝ)*(sp_s2_27) + (994616608783/250000000000 : ℝ)*(f.failure) + (1983805989959/200000000000 : ℝ)*(f.sum) + (8502646107406744281/21314167700000000000000000000000 : ℝ)*base62 + (22610839801037/179787500000000000000000000 : ℝ)*base65 + (125865415652259/423400000000000000000000000 : ℝ)*base67 + (1311999625029487/2876600000000000000000000000 : ℝ)*base68 + (3175735578624926159/19429275550000000000000000000000 : ℝ)*base71 + (333609128927929/1350850000000000000000000000 : ℝ)*base73 + (1299313036328263/2963800000000000000000000000 : ℝ)*base74 + (243097842040849/1350850000000000000000000000 : ℝ)*base76 + (1794902818499271391/2287799560000000000000000000000 : ℝ)*base79 + (20003/25000000000000000 : ℝ)*base86 + (20003/25000000000000000 : ℝ)*base88 + (20003/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30299/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(30299/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (205491068435642276126671987569/28792243437545000000000000000000000 : ℝ) := by norm_num
    linear_combination (243675434199/1000000000000 : ℝ)*(base40) + (785254287/4000000000 : ℝ)*(base49) + (66069344927/125000000000 : ℝ)*(base59) + (312752429219/50000000000 : ℝ)*(major_s2_0) + (312752429219/50000000000 : ℝ)*(major_s2_1) + (312752429219/50000000000 : ℝ)*(major_s2_2) + (9712169/500000000000 : ℝ)*(sp_s2_0) + (12364047/500000000000 : ℝ)*(sp_s2_2) + (1215759/100000000000 : ℝ)*(sp_s2_16) + (128015587/1000000000000 : ℝ)*(sp_s2_20) + (1785756697117/200000000000 : ℝ)*(sp_s2_21) + (2232200727481/250000000000 : ℝ)*(sp_s2_22) + (111609575303/12500000000 : ℝ)*(sp_s2_23) + (895290966059/250000000000 : ℝ)*(sp_s2_27) + (3581291879823/1000000000000 : ℝ)*(f.failure) + (2232200727481/250000000000 : ℝ)*(f.sum) + (378396322544149627/2131416770000000000000000000000 : ℝ)*base62 + (5903532808443/143830000000000000000000000 : ℝ)*base64 + (1000441783783/42340000000000000000000000 : ℝ)*base66 + (37529526208817/287660000000000000000000000 : ℝ)*base68 + (25553632339444553/777171022000000000000000000000 : ℝ)*base71 + (156971889304887/270170000000000000000000000 : ℝ)*base72 + (44728026933201/296380000000000000000000000 : ℝ)*base74 + (94925587491909/270170000000000000000000000 : ℝ)*base77 + (202014030571885233/228779956000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (5357/100000000000000000 : ℝ)*base87 + (5357/100000000000000000 : ℝ)*base89 + (5357/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((27017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14819/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14819/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14383/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14383/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13083/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13083/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15727/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15727/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30299/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(30299/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315053_s2 p hpa hpb X hX hprev1

#print axioms solution
