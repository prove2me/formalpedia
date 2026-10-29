-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311059_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:00:36.295105+00:00
-- url     : https://prove2.me/submissions/739c2fc2-11b5-4f57-b2f7-7550ae5caa02

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
theorem collision_support_c311059_s2_s2_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-669510311/2000000000 : ℝ)*x 0 + (3334112857/10000000000 : ℝ)*x 1 + (5797788/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669510311/2000000000 : ℝ)^9 ≤ (24486970997589/100000000000000 : ℝ)^7 := by
    have hnat : (669510311 : ℕ)^9*100000000000000^7 ≤ 24486970997589^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669510311 2000000000 24486970997589 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3334112857/10000000000 : ℝ)^9 ≤ (24360654498827/100000000000000 : ℝ)^7 := by
    have hnat : (3334112857 : ℕ)^9*100000000000000^7 ≤ 24360654498827^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3334112857 10000000000 24360654498827 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5797788/9765625 : ℝ)^9 ≤ (25576187245467/50000000000000 : ℝ)^7 := by
    have hnat : (5797788 : ℕ)^9*50000000000000^7 ≤ 25576187245467^7*9765625^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5797788 9765625 25576187245467 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-669510311/2000000000 : ℝ), (3334112857/10000000000 : ℝ), (5797788/9765625 : ℝ)] ![(24486970997589/100000000000000 : ℝ), (24360654498827/100000000000000 : ℝ), (25576187245467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-669510311/2000000000 : ℝ)|^9 ≤ (24486970997589/100000000000000 : ℝ)^7
        have hw : |(-669510311/2000000000 : ℝ)|=(669510311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3334112857/10000000000 : ℝ)|^9 ≤ (24360654498827/100000000000000 : ℝ)^7
        have hw : |(3334112857/10000000000 : ℝ)|=(3334112857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5797788/9765625 : ℝ)|^9 ≤ (25576187245467/50000000000000 : ℝ)^7
        have hw : |(5797788/9765625 : ℝ)|=(5797788/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (834066373/2500000000 : ℝ)*x 0 + (-51912061/156250000 : ℝ)*x 1 + (5956454453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834066373/2500000000 : ℝ)^9 ≤ (12190439168269/50000000000000 : ℝ)^7 := by
    have hnat : (834066373 : ℕ)^9*50000000000000^7 ≤ 12190439168269^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834066373 2500000000 12190439168269 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51912061/156250000 : ℝ)^9 ≤ (12125207433047/50000000000000 : ℝ)^7 := by
    have hnat : (51912061 : ℕ)^9*50000000000000^7 ≤ 12125207433047^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51912061 156250000 12125207433047 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5956454453/10000000000 : ℝ)^9 ≤ (200659010881/390625000000 : ℝ)^7 := by
    have hnat : (5956454453 : ℕ)^9*390625000000^7 ≤ 200659010881^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956454453 10000000000 200659010881 390625000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834066373/2500000000 : ℝ), (-51912061/156250000 : ℝ), (5956454453/10000000000 : ℝ)] ![(12190439168269/50000000000000 : ℝ), (12125207433047/50000000000000 : ℝ), (200659010881/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834066373/2500000000 : ℝ)|^9 ≤ (12190439168269/50000000000000 : ℝ)^7
        have hw : |(834066373/2500000000 : ℝ)|=(834066373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51912061/156250000 : ℝ)|^9 ≤ (12125207433047/50000000000000 : ℝ)^7
        have hw : |(-51912061/156250000 : ℝ)|=(51912061/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5956454453/10000000000 : ℝ)|^9 ≤ (200659010881/390625000000 : ℝ)^7
        have hw : |(5956454453/10000000000 : ℝ)|=(5956454453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2884318529/5000000000 : ℝ)*x 0 + (5548321389/10000000000 : ℝ)*x 1 + (-78851237/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2884318529/5000000000 : ℝ)^9 ≤ (4929562985521/10000000000000 : ℝ)^7 := by
    have hnat : (2884318529 : ℕ)^9*10000000000000^7 ≤ 4929562985521^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2884318529 5000000000 4929562985521 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5548321389/10000000000 : ℝ)^9 ≤ (2344417374397/5000000000000 : ℝ)^7 := by
    have hnat : (5548321389 : ℕ)^9*5000000000000^7 ≤ 2344417374397^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548321389 10000000000 2344417374397 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78851237/1000000000 : ℝ)^9 ≤ (3816022638589/100000000000000 : ℝ)^7 := by
    have hnat : (78851237 : ℕ)^9*100000000000000^7 ≤ 3816022638589^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78851237 1000000000 3816022638589 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2884318529/5000000000 : ℝ), (5548321389/10000000000 : ℝ), (-78851237/1000000000 : ℝ)] ![(4929562985521/10000000000000 : ℝ), (2344417374397/5000000000000 : ℝ), (3816022638589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2884318529/5000000000 : ℝ)|^9 ≤ (4929562985521/10000000000000 : ℝ)^7
        have hw : |(2884318529/5000000000 : ℝ)|=(2884318529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5548321389/10000000000 : ℝ)|^9 ≤ (2344417374397/5000000000000 : ℝ)^7
        have hw : |(5548321389/10000000000 : ℝ)|=(5548321389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78851237/1000000000 : ℝ)|^9 ≤ (3816022638589/100000000000000 : ℝ)^7
        have hw : |(-78851237/1000000000 : ℝ)|=(78851237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4234352743/10000000000 : ℝ)*x 0 + (4803843183/10000000000 : ℝ)*x 1 + (463341323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234352743/10000000000 : ℝ)^9 ≤ (33124913903459/100000000000000 : ℝ)^7 := by
    have hnat : (4234352743 : ℕ)^9*100000000000000^7 ≤ 33124913903459^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234352743 10000000000 33124913903459 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4803843183/10000000000 : ℝ)^9 ≤ (9739893500169/25000000000000 : ℝ)^7 := by
    have hnat : (4803843183 : ℕ)^9*25000000000000^7 ≤ 9739893500169^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803843183 10000000000 9739893500169 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (463341323/1250000000 : ℝ)^9 ≤ (5583102416009/20000000000000 : ℝ)^7 := by
    have hnat : (463341323 : ℕ)^9*20000000000000^7 ≤ 5583102416009^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463341323 1250000000 5583102416009 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234352743/10000000000 : ℝ), (4803843183/10000000000 : ℝ), (463341323/1250000000 : ℝ)] ![(33124913903459/100000000000000 : ℝ), (9739893500169/25000000000000 : ℝ), (5583102416009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234352743/10000000000 : ℝ)|^9 ≤ (33124913903459/100000000000000 : ℝ)^7
        have hw : |(4234352743/10000000000 : ℝ)|=(4234352743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4803843183/10000000000 : ℝ)|^9 ≤ (9739893500169/25000000000000 : ℝ)^7
        have hw : |(4803843183/10000000000 : ℝ)|=(4803843183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(463341323/1250000000 : ℝ)|^9 ≤ (5583102416009/20000000000000 : ℝ)^7
        have hw : |(463341323/1250000000 : ℝ)|=(463341323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3145350973/10000000000 : ℝ)*x 0 + (562895811/2000000000 : ℝ)*x 1 + (652930461/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3145350973/10000000000 : ℝ)^9 ≤ (22601954825049/100000000000000 : ℝ)^7 := by
    have hnat : (3145350973 : ℕ)^9*100000000000000^7 ≤ 22601954825049^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3145350973 10000000000 22601954825049 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562895811/2000000000 : ℝ)^9 ≤ (9796099197733/50000000000000 : ℝ)^7 := by
    have hnat : (562895811 : ℕ)^9*50000000000000^7 ≤ 9796099197733^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562895811 2000000000 9796099197733 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652930461/1000000000 : ℝ)^9 ≤ (57805846762271/100000000000000 : ℝ)^7 := by
    have hnat : (652930461 : ℕ)^9*100000000000000^7 ≤ 57805846762271^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652930461 1000000000 57805846762271 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3145350973/10000000000 : ℝ), (562895811/2000000000 : ℝ), (652930461/1000000000 : ℝ)] ![(22601954825049/100000000000000 : ℝ), (9796099197733/50000000000000 : ℝ), (57805846762271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3145350973/10000000000 : ℝ)|^9 ≤ (22601954825049/100000000000000 : ℝ)^7
        have hw : |(-3145350973/10000000000 : ℝ)|=(3145350973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562895811/2000000000 : ℝ)|^9 ≤ (9796099197733/50000000000000 : ℝ)^7
        have hw : |(562895811/2000000000 : ℝ)|=(562895811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652930461/1000000000 : ℝ)|^9 ≤ (57805846762271/100000000000000 : ℝ)^7
        have hw : |(652930461/1000000000 : ℝ)|=(652930461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3151056129/10000000000 : ℝ)*x 0 + (-2783567617/10000000000 : ℝ)*x 1 + (6548931347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3151056129/10000000000 : ℝ)^9 ≤ (22654677975581/100000000000000 : ℝ)^7 := by
    have hnat : (3151056129 : ℕ)^9*100000000000000^7 ≤ 22654677975581^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3151056129 10000000000 22654677975581 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2783567617/10000000000 : ℝ)^9 ≤ (19315972054497/100000000000000 : ℝ)^7 := by
    have hnat : (2783567617 : ℕ)^9*100000000000000^7 ≤ 19315972054497^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783567617 10000000000 19315972054497 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6548931347/10000000000 : ℝ)^9 ≤ (58029349954987/100000000000000 : ℝ)^7 := by
    have hnat : (6548931347 : ℕ)^9*100000000000000^7 ≤ 58029349954987^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6548931347 10000000000 58029349954987 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3151056129/10000000000 : ℝ), (-2783567617/10000000000 : ℝ), (6548931347/10000000000 : ℝ)] ![(22654677975581/100000000000000 : ℝ), (19315972054497/100000000000000 : ℝ), (58029349954987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3151056129/10000000000 : ℝ)|^9 ≤ (22654677975581/100000000000000 : ℝ)^7
        have hw : |(3151056129/10000000000 : ℝ)|=(3151056129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2783567617/10000000000 : ℝ)|^9 ≤ (19315972054497/100000000000000 : ℝ)^7
        have hw : |(-2783567617/10000000000 : ℝ)|=(2783567617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6548931347/10000000000 : ℝ)|^9 ≤ (58029349954987/100000000000000 : ℝ)^7
        have hw : |(6548931347/10000000000 : ℝ)|=(6548931347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5525075901/10000000000 : ℝ)*x 0 + (758033001/1250000000 : ℝ)*x 1 + (-4664283/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5525075901/10000000000 : ℝ)^9 ≤ (23317963040653/50000000000000 : ℝ)^7 := by
    have hnat : (5525075901 : ℕ)^9*50000000000000^7 ≤ 23317963040653^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525075901 10000000000 23317963040653 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758033001/1250000000 : ℝ)^9 ≤ (52567182474727/100000000000000 : ℝ)^7 := by
    have hnat : (758033001 : ℕ)^9*100000000000000^7 ≤ 52567182474727^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758033001 1250000000 52567182474727 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4664283/200000000 : ℝ)^9 ≤ (79689142491/10000000000000 : ℝ)^7 := by
    have hnat : (4664283 : ℕ)^9*10000000000000^7 ≤ 79689142491^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4664283 200000000 79689142491 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5525075901/10000000000 : ℝ), (758033001/1250000000 : ℝ), (-4664283/200000000 : ℝ)] ![(23317963040653/50000000000000 : ℝ), (52567182474727/100000000000000 : ℝ), (79689142491/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5525075901/10000000000 : ℝ)|^9 ≤ (23317963040653/50000000000000 : ℝ)^7
        have hw : |(5525075901/10000000000 : ℝ)|=(5525075901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(758033001/1250000000 : ℝ)|^9 ≤ (52567182474727/100000000000000 : ℝ)^7
        have hw : |(758033001/1250000000 : ℝ)|=(758033001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4664283/200000000 : ℝ)|^9 ≤ (79689142491/10000000000000 : ℝ)^7
        have hw : |(-4664283/200000000 : ℝ)|=(4664283/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1946917983/5000000000 : ℝ)*x 0 + (6198362437/10000000000 : ℝ)*x 1 + (485369181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946917983/5000000000 : ℝ)^9 ≤ (5948023714761/20000000000000 : ℝ)^7 := by
    have hnat : (1946917983 : ℕ)^9*20000000000000^7 ≤ 5948023714761^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946917983 5000000000 5948023714761 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6198362437/10000000000 : ℝ)^9 ≤ (27033204735211/50000000000000 : ℝ)^7 := by
    have hnat : (6198362437 : ℕ)^9*50000000000000^7 ≤ 27033204735211^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6198362437 10000000000 27033204735211 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485369181/2000000000 : ℝ)^9 ≤ (1012091996153/6250000000000 : ℝ)^7 := by
    have hnat : (485369181 : ℕ)^9*6250000000000^7 ≤ 1012091996153^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485369181 2000000000 1012091996153 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1946917983/5000000000 : ℝ), (6198362437/10000000000 : ℝ), (485369181/2000000000 : ℝ)] ![(5948023714761/20000000000000 : ℝ), (27033204735211/50000000000000 : ℝ), (1012091996153/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1946917983/5000000000 : ℝ)|^9 ≤ (5948023714761/20000000000000 : ℝ)^7
        have hw : |(1946917983/5000000000 : ℝ)|=(1946917983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6198362437/10000000000 : ℝ)|^9 ≤ (27033204735211/50000000000000 : ℝ)^7
        have hw : |(6198362437/10000000000 : ℝ)|=(6198362437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(485369181/2000000000 : ℝ)|^9 ≤ (1012091996153/6250000000000 : ℝ)^7
        have hw : |(485369181/2000000000 : ℝ)|=(485369181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-17589029/62500000 : ℝ)*x 0 + (157259091/500000000 : ℝ)*x 1 + (816203277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17589029/62500000 : ℝ)^9 ≤ (19590100374379/100000000000000 : ℝ)^7 := by
    have hnat : (17589029 : ℕ)^9*100000000000000^7 ≤ 19590100374379^7*62500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17589029 62500000 19590100374379 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157259091/500000000 : ℝ)^9 ≤ (22600392045473/100000000000000 : ℝ)^7 := by
    have hnat : (157259091 : ℕ)^9*100000000000000^7 ≤ 22600392045473^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157259091 500000000 22600392045473 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (816203277/1250000000 : ℝ)^9 ≤ (7226188445813/12500000000000 : ℝ)^7 := by
    have hnat : (816203277 : ℕ)^9*12500000000000^7 ≤ 7226188445813^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816203277 1250000000 7226188445813 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17589029/62500000 : ℝ), (157259091/500000000 : ℝ), (816203277/1250000000 : ℝ)] ![(19590100374379/100000000000000 : ℝ), (22600392045473/100000000000000 : ℝ), (7226188445813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17589029/62500000 : ℝ)|^9 ≤ (19590100374379/100000000000000 : ℝ)^7
        have hw : |(-17589029/62500000 : ℝ)|=(17589029/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157259091/500000000 : ℝ)|^9 ≤ (22600392045473/100000000000000 : ℝ)^7
        have hw : |(157259091/500000000 : ℝ)|=(157259091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(816203277/1250000000 : ℝ)|^9 ≤ (7226188445813/12500000000000 : ℝ)^7
        have hw : |(816203277/1250000000 : ℝ)|=(816203277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2802642199/10000000000 : ℝ)*x 0 + (-1566107503/5000000000 : ℝ)*x 1 + (3274626491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2802642199/10000000000 : ℝ)^9 ≤ (19486320643439/100000000000000 : ℝ)^7 := by
    have hnat : (2802642199 : ℕ)^9*100000000000000^7 ≤ 19486320643439^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802642199 10000000000 19486320643439 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1566107503/5000000000 : ℝ)^9 ≤ (22480665113/100000000000 : ℝ)^7 := by
    have hnat : (1566107503 : ℕ)^9*100000000000^7 ≤ 22480665113^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566107503 5000000000 22480665113 100000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3274626491/5000000000 : ℝ)^9 ≤ (29016507115107/50000000000000 : ℝ)^7 := by
    have hnat : (3274626491 : ℕ)^9*50000000000000^7 ≤ 29016507115107^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3274626491 5000000000 29016507115107 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2802642199/10000000000 : ℝ), (-1566107503/5000000000 : ℝ), (3274626491/5000000000 : ℝ)] ![(19486320643439/100000000000000 : ℝ), (22480665113/100000000000 : ℝ), (29016507115107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2802642199/10000000000 : ℝ)|^9 ≤ (19486320643439/100000000000000 : ℝ)^7
        have hw : |(2802642199/10000000000 : ℝ)|=(2802642199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1566107503/5000000000 : ℝ)|^9 ≤ (22480665113/100000000000 : ℝ)^7
        have hw : |(-1566107503/5000000000 : ℝ)|=(1566107503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3274626491/5000000000 : ℝ)|^9 ≤ (29016507115107/50000000000000 : ℝ)^7
        have hw : |(3274626491/5000000000 : ℝ)|=(3274626491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (253142961/400000000 : ℝ)*x 0 + (5250118519/10000000000 : ℝ)*x 1 + (-116446271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253142961/400000000 : ℝ)^9 ≤ (55531078899637/100000000000000 : ℝ)^7 := by
    have hnat : (253142961 : ℕ)^9*100000000000000^7 ≤ 55531078899637^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253142961 400000000 55531078899637 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5250118519/10000000000 : ℝ)^9 ≤ (8734688459797/20000000000000 : ℝ)^7 := by
    have hnat : (5250118519 : ℕ)^9*20000000000000^7 ≤ 8734688459797^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250118519 10000000000 8734688459797 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116446271/5000000000 : ℝ)^9 ≤ (198869697467/25000000000000 : ℝ)^7 := by
    have hnat : (116446271 : ℕ)^9*25000000000000^7 ≤ 198869697467^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116446271 5000000000 198869697467 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(253142961/400000000 : ℝ), (5250118519/10000000000 : ℝ), (-116446271/5000000000 : ℝ)] ![(55531078899637/100000000000000 : ℝ), (8734688459797/20000000000000 : ℝ), (198869697467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(253142961/400000000 : ℝ)|^9 ≤ (55531078899637/100000000000000 : ℝ)^7
        have hw : |(253142961/400000000 : ℝ)|=(253142961/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5250118519/10000000000 : ℝ)|^9 ≤ (8734688459797/20000000000000 : ℝ)^7
        have hw : |(5250118519/10000000000 : ℝ)|=(5250118519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116446271/5000000000 : ℝ)|^9 ≤ (198869697467/25000000000000 : ℝ)^7
        have hw : |(-116446271/5000000000 : ℝ)|=(116446271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5550808741/10000000000 : ℝ)*x 0 + (4604892611/10000000000 : ℝ)*x 1 + (2426110297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5550808741/10000000000 : ℝ)^9 ≤ (23457687710847/50000000000000 : ℝ)^7 := by
    have hnat : (5550808741 : ℕ)^9*50000000000000^7 ≤ 23457687710847^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5550808741 10000000000 23457687710847 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4604892611/10000000000 : ℝ)^9 ≤ (36897463221593/100000000000000 : ℝ)^7 := by
    have hnat : (4604892611 : ℕ)^9*100000000000000^7 ≤ 36897463221593^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604892611 10000000000 36897463221593 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2426110297/10000000000 : ℝ)^9 ≤ (404679033743/2500000000000 : ℝ)^7 := by
    have hnat : (2426110297 : ℕ)^9*2500000000000^7 ≤ 404679033743^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426110297 10000000000 404679033743 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5550808741/10000000000 : ℝ), (4604892611/10000000000 : ℝ), (2426110297/10000000000 : ℝ)] ![(23457687710847/50000000000000 : ℝ), (36897463221593/100000000000000 : ℝ), (404679033743/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5550808741/10000000000 : ℝ)|^9 ≤ (23457687710847/50000000000000 : ℝ)^7
        have hw : |(5550808741/10000000000 : ℝ)|=(5550808741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4604892611/10000000000 : ℝ)|^9 ≤ (36897463221593/100000000000000 : ℝ)^7
        have hw : |(4604892611/10000000000 : ℝ)|=(4604892611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2426110297/10000000000 : ℝ)|^9 ≤ (404679033743/2500000000000 : ℝ)^7
        have hw : |(2426110297/10000000000 : ℝ)|=(2426110297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1682505511/5000000000 : ℝ)*x 0 + (1676725353/5000000000 : ℝ)*x 1 + (738208117/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1682505511/5000000000 : ℝ)^9 ≤ (12325648503481/50000000000000 : ℝ)^7 := by
    have hnat : (1682505511 : ℕ)^9*50000000000000^7 ≤ 12325648503481^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682505511 5000000000 12325648503481 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1676725353/5000000000 : ℝ)^9 ≤ (6135616409693/25000000000000 : ℝ)^7 := by
    have hnat : (1676725353 : ℕ)^9*25000000000000^7 ≤ 6135616409693^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676725353 5000000000 6135616409693 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738208117/1250000000 : ℝ)^9 ≤ (12701559334527/25000000000000 : ℝ)^7 := by
    have hnat : (738208117 : ℕ)^9*25000000000000^7 ≤ 12701559334527^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738208117 1250000000 12701559334527 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1682505511/5000000000 : ℝ), (1676725353/5000000000 : ℝ), (738208117/1250000000 : ℝ)] ![(12325648503481/50000000000000 : ℝ), (6135616409693/25000000000000 : ℝ), (12701559334527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1682505511/5000000000 : ℝ)|^9 ≤ (12325648503481/50000000000000 : ℝ)^7
        have hw : |(-1682505511/5000000000 : ℝ)|=(1682505511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1676725353/5000000000 : ℝ)|^9 ≤ (6135616409693/25000000000000 : ℝ)^7
        have hw : |(1676725353/5000000000 : ℝ)|=(1676725353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738208117/1250000000 : ℝ)|^9 ≤ (12701559334527/25000000000000 : ℝ)^7
        have hw : |(738208117/1250000000 : ℝ)|=(738208117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3355651167/10000000000 : ℝ)*x 0 + (-3339724861/10000000000 : ℝ)*x 1 + (1481323133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3355651167/10000000000 : ℝ)^9 ≤ (1228158650841/5000000000000 : ℝ)^7 := by
    have hnat : (3355651167 : ℕ)^9*5000000000000^7 ≤ 1228158650841^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3355651167 10000000000 1228158650841 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3339724861/10000000000 : ℝ)^9 ≤ (2441338664809/10000000000000 : ℝ)^7 := by
    have hnat : (3339724861 : ℕ)^9*10000000000000^7 ≤ 2441338664809^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3339724861 10000000000 2441338664809 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1481323133/2500000000 : ℝ)^9 ≤ (10204688065217/20000000000000 : ℝ)^7 := by
    have hnat : (1481323133 : ℕ)^9*20000000000000^7 ≤ 10204688065217^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481323133 2500000000 10204688065217 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3355651167/10000000000 : ℝ), (-3339724861/10000000000 : ℝ), (1481323133/2500000000 : ℝ)] ![(1228158650841/5000000000000 : ℝ), (2441338664809/10000000000000 : ℝ), (10204688065217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3355651167/10000000000 : ℝ)|^9 ≤ (1228158650841/5000000000000 : ℝ)^7
        have hw : |(3355651167/10000000000 : ℝ)|=(3355651167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3339724861/10000000000 : ℝ)|^9 ≤ (2441338664809/10000000000000 : ℝ)^7
        have hw : |(-3339724861/10000000000 : ℝ)|=(3339724861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1481323133/2500000000 : ℝ)|^9 ≤ (10204688065217/20000000000000 : ℝ)^7
        have hw : |(1481323133/2500000000 : ℝ)|=(1481323133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6642084727/10000000000 : ℝ)*x 0 + (294949641/625000000 : ℝ)*x 1 + (-312303177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6642084727/10000000000 : ℝ)^9 ≤ (29546377840237/50000000000000 : ℝ)^7 := by
    have hnat : (6642084727 : ℕ)^9*50000000000000^7 ≤ 29546377840237^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6642084727 10000000000 29546377840237 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294949641/625000000 : ℝ)^9 ≤ (38079149652973/100000000000000 : ℝ)^7 := by
    have hnat : (294949641 : ℕ)^9*100000000000000^7 ≤ 38079149652973^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294949641 625000000 38079149652973 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312303177/5000000000 : ℝ)^9 ≤ (1414047324799/50000000000000 : ℝ)^7 := by
    have hnat : (312303177 : ℕ)^9*50000000000000^7 ≤ 1414047324799^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312303177 5000000000 1414047324799 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6642084727/10000000000 : ℝ), (294949641/625000000 : ℝ), (-312303177/5000000000 : ℝ)] ![(29546377840237/50000000000000 : ℝ), (38079149652973/100000000000000 : ℝ), (1414047324799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6642084727/10000000000 : ℝ)|^9 ≤ (29546377840237/50000000000000 : ℝ)^7
        have hw : |(6642084727/10000000000 : ℝ)|=(6642084727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(294949641/625000000 : ℝ)|^9 ≤ (38079149652973/100000000000000 : ℝ)^7
        have hw : |(294949641/625000000 : ℝ)|=(294949641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-312303177/5000000000 : ℝ)|^9 ≤ (1414047324799/50000000000000 : ℝ)^7
        have hw : |(-312303177/5000000000 : ℝ)|=(312303177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311059_s2_s2_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2309534877/10000000000 : ℝ)*x 0 + (6769964621/10000000000 : ℝ)*x 1 + (207621427/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2309534877/10000000000 : ℝ)^9 ≤ (15194079322021/100000000000000 : ℝ)^7 := by
    have hnat : (2309534877 : ℕ)^9*100000000000000^7 ≤ 15194079322021^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309534877 10000000000 15194079322021 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6769964621/10000000000 : ℝ)^9 ≤ (30279766198713/50000000000000 : ℝ)^7 := by
    have hnat : (6769964621 : ℕ)^9*50000000000000^7 ≤ 30279766198713^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6769964621 10000000000 30279766198713 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207621427/625000000 : ℝ)^9 ≤ (24246388274723/100000000000000 : ℝ)^7 := by
    have hnat : (207621427 : ℕ)^9*100000000000000^7 ≤ 24246388274723^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207621427 625000000 24246388274723 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2309534877/10000000000 : ℝ), (6769964621/10000000000 : ℝ), (207621427/625000000 : ℝ)] ![(15194079322021/100000000000000 : ℝ), (30279766198713/50000000000000 : ℝ), (24246388274723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2309534877/10000000000 : ℝ)|^9 ≤ (15194079322021/100000000000000 : ℝ)^7
        have hw : |(2309534877/10000000000 : ℝ)|=(2309534877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6769964621/10000000000 : ℝ)|^9 ≤ (30279766198713/50000000000000 : ℝ)^7
        have hw : |(6769964621/10000000000 : ℝ)|=(6769964621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207621427/625000000 : ℝ)|^9 ≤ (24246388274723/100000000000000 : ℝ)^7
        have hw : |(207621427/625000000 : ℝ)|=(207621427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311059_s2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((9067/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9067/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71207/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(71207/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(47679/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(47679/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3767/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3767/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3413/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3413/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (9067/12500 : ℝ) ^ (71/16 : ℝ) ≤ (24055069282467203381/100000000000000000000 : ℝ) := by
    have hpowers : (9067/12500 : ℝ)^71 ≤ (24055069282467203381/100000000000000000000 : ℝ)^16 := by
      have hnat : (9067 : ℕ)^71*100000000000000000000^16 ≤ 24055069282467203381^16*12500^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9067 12500 24055069282467203381 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9067/12500 : ℝ)) (X := (24055069282467203381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (124055069282467203381/100000000000000000000 : ℝ) ≤ (10497750069547651/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (124055069282467203381/100000000000000000000 : ℝ)^16 ≤ (10497750069547651/10000000000000000 : ℝ)^71 := by
      have hnat : (124055069282467203381 : ℕ)^16*10000000000000000^71 ≤ 10497750069547651^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124055069282467203381 100000000000000000000 10497750069547651 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10497750069547651/10000000000000000 : ℝ)) (X := (124055069282467203381/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (74055069282467203381/50000000000000000000 : ℝ) ≤ (5462754038388717/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (74055069282467203381/50000000000000000000 : ℝ)^16 ≤ (5462754038388717/5000000000000000 : ℝ)^71 := by
      have hnat : (74055069282467203381 : ℕ)^16*5000000000000000^71 ≤ 5462754038388717^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74055069282467203381 50000000000000000000 5462754038388717 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5462754038388717/5000000000000000 : ℝ)) (X := (74055069282467203381/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(497750069547651/7253600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(427758007229783/7253600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (9067/12500 : ℝ)) (alpha := (497750069547651/7253600000000000 : ℝ)) (beta := (427758007229783/7253600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9067/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(497750069547651/7253600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(427758007229783/7253600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (71207/100000 : ℝ) ^ (71/16 : ℝ) ≤ (1107999174694684619/5000000000000000000 : ℝ) := by
    have hpowers : (71207/100000 : ℝ)^71 ≤ (1107999174694684619/5000000000000000000 : ℝ)^16 := by
      have hnat : (71207 : ℕ)^71*5000000000000000000^16 ≤ 1107999174694684619^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71207 100000 1107999174694684619 5000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71207/100000 : ℝ)) (X := (1107999174694684619/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (6107999174694684619/5000000000000000000 : ℝ) ≤ (523069780782471/500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (6107999174694684619/5000000000000000000 : ℝ)^16 ≤ (523069780782471/500000000000000 : ℝ)^71 := by
      have hnat : (6107999174694684619 : ℕ)^16*500000000000000^71 ≤ 523069780782471^71*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6107999174694684619 5000000000000000000 523069780782471 500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (523069780782471/500000000000000 : ℝ)) (X := (6107999174694684619/5000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (3607999174694684619/2500000000000000000 : ℝ) ≤ (1357733577738393/1250000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3607999174694684619/2500000000000000000 : ℝ)^16 ≤ (1357733577738393/1250000000000000 : ℝ)^71 := by
      have hnat : (3607999174694684619 : ℕ)^16*1250000000000000^71 ≤ 1357733577738393^71*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3607999174694684619 2500000000000000000 1357733577738393 1250000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1357733577738393/1250000000000000 : ℝ)) (X := (3607999174694684619/2500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(23069780782471/356035000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(100118251564431/1780175000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (71207/100000 : ℝ)) (alpha := (23069780782471/356035000000000 : ℝ)) (beta := (100118251564431/1780175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (71207/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(23069780782471/356035000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(100118251564431/1780175000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (47679/100000 : ℝ) ^ (71/16 : ℝ) ≤ (9343652625413523/250000000000000000 : ℝ) := by
    have hpowers : (47679/100000 : ℝ)^71 ≤ (9343652625413523/250000000000000000 : ℝ)^16 := by
      have hnat : (47679 : ℕ)^71*250000000000000000^16 ≤ 9343652625413523^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47679 100000 9343652625413523 250000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47679/100000 : ℝ)) (X := (9343652625413523/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (259343652625413523/250000000000000000 : ℝ) ≤ (2016606302081619/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (259343652625413523/250000000000000000 : ℝ)^16 ≤ (2016606302081619/2000000000000000 : ℝ)^71 := by
      have hnat : (259343652625413523 : ℕ)^16*2000000000000000^71 ≤ 2016606302081619^71*250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        259343652625413523 250000000000000000 2016606302081619 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2016606302081619/2000000000000000 : ℝ)) (X := (259343652625413523/250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (134343652625413523/125000000000000000 : ℝ) ≤ (10163777050138161/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (134343652625413523/125000000000000000 : ℝ)^16 ≤ (10163777050138161/10000000000000000 : ℝ)^71 := by
      have hnat : (134343652625413523 : ℕ)^16*10000000000000000^71 ≤ 10163777050138161^71*125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        134343652625413523 125000000000000000 10163777050138161 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10163777050138161/10000000000000000 : ℝ)) (X := (134343652625413523/125000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(16606302081619/953580000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(13457589955011/794650000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (47679/100000 : ℝ)) (alpha := (16606302081619/953580000000000 : ℝ)) (beta := (13457589955011/794650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (47679/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(16606302081619/953580000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(13457589955011/794650000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-669510311/2000000000 : ℝ)*X 0 0+(3334112857/10000000000 : ℝ)*X 0 1+(5797788/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((834066373/2500000000 : ℝ)*X 1 0+(-51912061/156250000 : ℝ)*X 1 1+(5956454453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2884318529/5000000000 : ℝ)*X 2 0+(5548321389/10000000000 : ℝ)*X 2 1+(-78851237/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4234352743/10000000000 : ℝ)*X 0 0+(4803843183/10000000000 : ℝ)*X 0 1+(463341323/1250000000 : ℝ)*X 0 2+(4234352743/10000000000 : ℝ)*X 1 0+(4803843183/10000000000 : ℝ)*X 1 1+(463341323/1250000000 : ℝ)*X 1 2+(4234352743/10000000000 : ℝ)*X 2 0+(4803843183/10000000000 : ℝ)*X 2 1+(463341323/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-3145350973/10000000000 : ℝ)*X 0 0+(562895811/2000000000 : ℝ)*X 0 1+(652930461/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3151056129/10000000000 : ℝ)*X 1 0+(-2783567617/10000000000 : ℝ)*X 1 1+(6548931347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5525075901/10000000000 : ℝ)*X 2 0+(758033001/1250000000 : ℝ)*X 2 1+(-4664283/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1946917983/5000000000 : ℝ)*X 0 0+(6198362437/10000000000 : ℝ)*X 0 1+(485369181/2000000000 : ℝ)*X 0 2+(1946917983/5000000000 : ℝ)*X 1 0+(6198362437/10000000000 : ℝ)*X 1 1+(485369181/2000000000 : ℝ)*X 1 2+(1946917983/5000000000 : ℝ)*X 2 0+(6198362437/10000000000 : ℝ)*X 2 1+(485369181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-17589029/62500000 : ℝ)*X 0 0+(157259091/500000000 : ℝ)*X 0 1+(816203277/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2802642199/10000000000 : ℝ)*X 1 0+(-1566107503/5000000000 : ℝ)*X 1 1+(3274626491/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((253142961/400000000 : ℝ)*X 2 0+(5250118519/10000000000 : ℝ)*X 2 1+(-116446271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((5550808741/10000000000 : ℝ)*X 0 0+(4604892611/10000000000 : ℝ)*X 0 1+(2426110297/10000000000 : ℝ)*X 0 2+(5550808741/10000000000 : ℝ)*X 1 0+(4604892611/10000000000 : ℝ)*X 1 1+(2426110297/10000000000 : ℝ)*X 1 2+(5550808741/10000000000 : ℝ)*X 2 0+(4604892611/10000000000 : ℝ)*X 2 1+(2426110297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1682505511/5000000000 : ℝ)*X 0 0+(1676725353/5000000000 : ℝ)*X 0 1+(738208117/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3355651167/10000000000 : ℝ)*X 1 0+(-3339724861/10000000000 : ℝ)*X 1 1+(1481323133/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((6642084727/10000000000 : ℝ)*X 2 0+(294949641/625000000 : ℝ)*X 2 1+(-312303177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2309534877/10000000000 : ℝ)*X 0 0+(6769964621/10000000000 : ℝ)*X 0 1+(207621427/625000000 : ℝ)*X 0 2+(2309534877/10000000000 : ℝ)*X 1 0+(6769964621/10000000000 : ℝ)*X 1 1+(207621427/625000000 : ℝ)*X 1 2+(2309534877/10000000000 : ℝ)*X 2 0+(6769964621/10000000000 : ℝ)*X 2 1+(207621427/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311059_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((38741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (194605668774892563591062213/14146160637500000000000000000000 : ℝ) := by norm_num
    linear_combination (7979771/1000000000000 : ℝ)*(base59) + (65133429697/40000000000 : ℝ)*(base60) + (6562088869507/1000000000000 : ℝ)*(major_s2_0) + (6562088869507/1000000000000 : ℝ)*(major_s2_1) + (6562088869507/1000000000000 : ℝ)*(major_s2_2) + (477819/31250000000 : ℝ)*(sp_s2_0) + (6874407/500000000000 : ℝ)*(sp_s2_1) + (72143021/1000000000000 : ℝ)*(sp_s2_2) + (4565678345801/500000000000 : ℝ)*(sp_s2_7) + (1141402314123/125000000000 : ℝ)*(sp_s2_8) + (9131299838789/1000000000000 : ℝ)*(sp_s2_9) + (3992757857289/1000000000000 : ℝ)*(sp_s2_13) + (139720013/1000000000000 : ℝ)*(sp_s2_15) + (21657157/500000000000 : ℝ)*(sp_s2_27) + (998200292901/250000000000 : ℝ)*(f.failure) + (913137198181/100000000000 : ℝ)*(f.sum) + (758406217116894983/2716062842400000000000000000000 : ℝ)*base62 + (54341877327767/198662500000000000000000000 : ℝ)*base64 + (1214809809857219/3560350000000000000000000000 : ℝ)*base67 + (360043384180387/953580000000000000000000000 : ℝ)*base68 + (4051528240908524711/23056292960000000000000000000000 : ℝ)*base70 + (2234050587167659/7253600000000000000000000000 : ℝ)*base72 + (267573412231181/712070000000000000000000000 : ℝ)*base75 + (3765892433101577/7253600000000000000000000000 : ℝ)*base77 + (12291305817524454711/103301419040000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (4637/6250000000000000 : ℝ)*base87 + (4637/6250000000000000 : ℝ)*base89 + (4637/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3767/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3767/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3801631833212890439054291683583/205221181600340000000000000000000000 : ℝ) := by norm_num
    linear_combination (5541584183/62500000000 : ℝ)*(base59) + (207399507017/125000000000 : ℝ)*(base60) + (3255349022177/500000000000 : ℝ)*(major_s2_0) + (3255349022177/500000000000 : ℝ)*(major_s2_1) + (3255349022177/500000000000 : ℝ)*(major_s2_2) + (9484353/500000000000 : ℝ)*(sp_s2_0) + (17860607/1000000000000 : ℝ)*(sp_s2_1) + (10117583/250000000000 : ℝ)*(sp_s2_6) + (49255929/250000000000 : ℝ)*(sp_s2_7) + (9059642266433/1000000000000 : ℝ)*(sp_s2_14) + (1132480049781/125000000000 : ℝ)*(sp_s2_15) + (1132465345587/125000000000 : ℝ)*(sp_s2_16) + (792298236933/200000000000 : ℝ)*(sp_s2_20) + (135494159/1000000000000 : ℝ)*(sp_s2_23) + (3961531654997/1000000000000 : ℝ)*(f.failure) + (1811971651771/200000000000 : ℝ)*(f.sum) + (706276781210851993/2121924095625000000000000000000 : ℝ)*base62 + (592465356976251/794650000000000000000000000 : ℝ)*base64 + (312147921427207/3560350000000000000000000000 : ℝ)*base66 + (72074608961143/238395000000000000000000000 : ℝ)*base68 + (8917374458059529061/11528146480000000000000000000000 : ℝ)*base70 + (183755263674409/3626800000000000000000000000 : ℝ)*base72 + (8224965302237/71207000000000000000000000 : ℝ)*base74 + (370008761221093/3626800000000000000000000000 : ℝ)*base76 + (5527502533612199467/51650709520000000000000000000000 : ℝ)*base78 + (11739/25000000000000000 : ℝ)*base87 + (11739/25000000000000000 : ℝ)*base89 + (11739/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3413/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3413/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (458818886382954916215349879737/35690640278320000000000000000000000 : ℝ) := by norm_num
    linear_combination (611599/250000000000 : ℝ)*(base11) + (1503829/1000000000000 : ℝ)*(base40) + (3389307/1000000000000 : ℝ)*(base50) + (584448200283/1000000000000 : ℝ)*(base60) + (4224013484577/1000000000000 : ℝ)*(major_s2_0) + (4224013484577/1000000000000 : ℝ)*(major_s2_1) + (4224013484577/1000000000000 : ℝ)*(major_s2_2) + (6151339/125000000000 : ℝ)*(sp_s2_2) + (40199437/500000000000 : ℝ)*(sp_s2_13) + (81303289/1000000000000 : ℝ)*(sp_s2_16) + (2938928011149/500000000000 : ℝ)*(sp_s2_21) + (2938929234347/500000000000 : ℝ)*(sp_s2_22) + (5877727954693/1000000000000 : ℝ)*(sp_s2_23) + (642520954109/250000000000 : ℝ)*(sp_s2_27) + (257016421531/100000000000 : ℝ)*(f.failure) + (2938929234347/500000000000 : ℝ)*(f.sum) + (416630780711066901/984080740000000000000000000000 : ℝ)*base62 + (12838432171121/34550000000000000000000000 : ℝ)*base64 + (5173253113459/55630468750000000000000000 : ℝ)*base66 + (881468923671/2764000000000000000000000 : ℝ)*base68 + (488348684910309547/1002447520000000000000000000000 : ℝ)*base70 + (1195204095428009/7253600000000000000000000000 : ℝ)*base72 + (117166903490991/356035000000000000000000000 : ℝ)*base74 + (2510025775248333/7253600000000000000000000000 : ℝ)*base76 + (2159331187221824009/20660283808000000000000000000000 : ℝ)*base79 + (1697/2500000000000000 : ℝ)*base87 + (1697/2500000000000000 : ℝ)*base89 + (1697/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((9067/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9067/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71207/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(71207/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(47679/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(47679/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3767/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3767/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3413/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3413/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311059_s2 p hpa hpb X hX hprev1

#print axioms solution
