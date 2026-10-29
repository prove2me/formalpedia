-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306060_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:58:08.125288+00:00
-- url     : https://prove2.me/submissions/2a0a64fe-b970-498c-9ec4-1dd47ce076de

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
theorem collision_support_c306060_s2_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-832008397/5000000000 : ℝ)*x 0 + (4542568797/10000000000 : ℝ)*x 1 + (-1582542057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832008397/5000000000 : ℝ)^135 ≤ (4766035662409/50000000000000 : ℝ)^103 := by
    have hnat : (832008397 : ℕ)^135*50000000000000^103 ≤ 4766035662409^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832008397 5000000000 4766035662409 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542568797/10000000000 : ℝ)^135 ≤ (35549384081643/100000000000000 : ℝ)^103 := by
    have hnat : (4542568797 : ℕ)^135*100000000000000^103 ≤ 35549384081643^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542568797 10000000000 35549384081643 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1582542057/2500000000 : ℝ)^135 ≤ (54918544588229/100000000000000 : ℝ)^103 := by
    have hnat : (1582542057 : ℕ)^135*100000000000000^103 ≤ 54918544588229^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582542057 2500000000 54918544588229 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-832008397/5000000000 : ℝ), (4542568797/10000000000 : ℝ), (-1582542057/2500000000 : ℝ)] ![(4766035662409/50000000000000 : ℝ), (35549384081643/100000000000000 : ℝ), (54918544588229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-832008397/5000000000 : ℝ)|^135 ≤ (4766035662409/50000000000000 : ℝ)^103
        have hw : |(-832008397/5000000000 : ℝ)|=(832008397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542568797/10000000000 : ℝ)|^135 ≤ (35549384081643/100000000000000 : ℝ)^103
        have hw : |(4542568797/10000000000 : ℝ)|=(4542568797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1582542057/2500000000 : ℝ)|^135 ≤ (54918544588229/100000000000000 : ℝ)^103
        have hw : |(-1582542057/2500000000 : ℝ)|=(1582542057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4533780603/10000000000 : ℝ)*x 0 + (-1667135821/10000000000 : ℝ)*x 1 + (-6336032301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4533780603/10000000000 : ℝ)^135 ≤ (7091853855117/20000000000000 : ℝ)^103 := by
    have hnat : (4533780603 : ℕ)^135*20000000000000^103 ≤ 7091853855117^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533780603 10000000000 7091853855117 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1667135821/10000000000 : ℝ)^135 ≤ (9555495895301/100000000000000 : ℝ)^103 := by
    have hnat : (1667135821 : ℕ)^135*100000000000000^103 ≤ 9555495895301^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667135821 10000000000 9555495895301 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6336032301/10000000000 : ℝ)^135 ≤ (27492617404681/50000000000000 : ℝ)^103 := by
    have hnat : (6336032301 : ℕ)^135*50000000000000^103 ≤ 27492617404681^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6336032301 10000000000 27492617404681 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4533780603/10000000000 : ℝ), (-1667135821/10000000000 : ℝ), (-6336032301/10000000000 : ℝ)] ![(7091853855117/20000000000000 : ℝ), (9555495895301/100000000000000 : ℝ), (27492617404681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4533780603/10000000000 : ℝ)|^135 ≤ (7091853855117/20000000000000 : ℝ)^103
        have hw : |(4533780603/10000000000 : ℝ)|=(4533780603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1667135821/10000000000 : ℝ)|^135 ≤ (9555495895301/100000000000000 : ℝ)^103
        have hw : |(-1667135821/10000000000 : ℝ)|=(1667135821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6336032301/10000000000 : ℝ)|^135 ≤ (27492617404681/50000000000000 : ℝ)^103
        have hw : |(-6336032301/10000000000 : ℝ)|=(6336032301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1576043529/10000000000 : ℝ)*x 0 + (100614083/400000000 : ℝ)*x 1 + (-8008075907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1576043529/10000000000 : ℝ)^135 ≤ (4438528522399/50000000000000 : ℝ)^103 := by
    have hnat : (1576043529 : ℕ)^135*50000000000000^103 ≤ 4438528522399^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576043529 10000000000 4438528522399 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100614083/400000000 : ℝ)^135 ≤ (16382381847367/100000000000000 : ℝ)^103 := by
    have hnat : (100614083 : ℕ)^135*100000000000000^103 ≤ 16382381847367^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100614083 400000000 16382381847367 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8008075907/10000000000 : ℝ)^135 ≤ (14948112218007/20000000000000 : ℝ)^103 := by
    have hnat : (8008075907 : ℕ)^135*20000000000000^103 ≤ 14948112218007^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8008075907 10000000000 14948112218007 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1576043529/10000000000 : ℝ), (100614083/400000000 : ℝ), (-8008075907/10000000000 : ℝ)] ![(4438528522399/50000000000000 : ℝ), (16382381847367/100000000000000 : ℝ), (14948112218007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1576043529/10000000000 : ℝ)|^135 ≤ (4438528522399/50000000000000 : ℝ)^103
        have hw : |(-1576043529/10000000000 : ℝ)|=(1576043529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100614083/400000000 : ℝ)|^135 ≤ (16382381847367/100000000000000 : ℝ)^103
        have hw : |(100614083/400000000 : ℝ)|=(100614083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8008075907/10000000000 : ℝ)|^135 ≤ (14948112218007/20000000000000 : ℝ)^103
        have hw : |(-8008075907/10000000000 : ℝ)|=(8008075907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (718941143/2500000000 : ℝ)*x 0 + (-557880797/5000000000 : ℝ)*x 1 + (-4007674597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (718941143/2500000000 : ℝ)^135 ≤ (1952535881503/10000000000000 : ℝ)^103 := by
    have hnat : (718941143 : ℕ)^135*10000000000000^103 ≤ 1952535881503^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718941143 2500000000 1952535881503 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557880797/5000000000 : ℝ)^135 ≤ (5645095109063/100000000000000 : ℝ)^103 := by
    have hnat : (557880797 : ℕ)^135*100000000000000^103 ≤ 5645095109063^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557880797 5000000000 5645095109063 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4007674597/5000000000 : ℝ)^135 ≤ (14965909213609/20000000000000 : ℝ)^103 := by
    have hnat : (4007674597 : ℕ)^135*20000000000000^103 ≤ 14965909213609^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007674597 5000000000 14965909213609 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(718941143/2500000000 : ℝ), (-557880797/5000000000 : ℝ), (-4007674597/5000000000 : ℝ)] ![(1952535881503/10000000000000 : ℝ), (5645095109063/100000000000000 : ℝ), (14965909213609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(718941143/2500000000 : ℝ)|^135 ≤ (1952535881503/10000000000000 : ℝ)^103
        have hw : |(718941143/2500000000 : ℝ)|=(718941143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557880797/5000000000 : ℝ)|^135 ≤ (5645095109063/100000000000000 : ℝ)^103
        have hw : |(-557880797/5000000000 : ℝ)|=(557880797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4007674597/5000000000 : ℝ)|^135 ≤ (14965909213609/20000000000000 : ℝ)^103
        have hw : |(-4007674597/5000000000 : ℝ)|=(4007674597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (357472911/1250000000 : ℝ)*x 0 + (7727724103/10000000000 : ℝ)*x 1 + (1631255041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357472911/1250000000 : ℝ)^135 ≤ (19383263958843/100000000000000 : ℝ)^103 := by
    have hnat : (357472911 : ℕ)^135*100000000000000^103 ≤ 19383263958843^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357472911 1250000000 19383263958843 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7727724103/10000000000 : ℝ)^135 ≤ (71329885285031/100000000000000 : ℝ)^103 := by
    have hnat : (7727724103 : ℕ)^135*100000000000000^103 ≤ 71329885285031^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7727724103 10000000000 71329885285031 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1631255041/10000000000 : ℝ)^135 ≤ (2321712688253/25000000000000 : ℝ)^103 := by
    have hnat : (1631255041 : ℕ)^135*25000000000000^103 ≤ 2321712688253^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631255041 10000000000 2321712688253 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(357472911/1250000000 : ℝ), (7727724103/10000000000 : ℝ), (1631255041/10000000000 : ℝ)] ![(19383263958843/100000000000000 : ℝ), (71329885285031/100000000000000 : ℝ), (2321712688253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(357472911/1250000000 : ℝ)|^135 ≤ (19383263958843/100000000000000 : ℝ)^103
        have hw : |(357472911/1250000000 : ℝ)|=(357472911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7727724103/10000000000 : ℝ)|^135 ≤ (71329885285031/100000000000000 : ℝ)^103
        have hw : |(7727724103/10000000000 : ℝ)|=(7727724103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1631255041/10000000000 : ℝ)|^135 ≤ (2321712688253/25000000000000 : ℝ)^103
        have hw : |(1631255041/10000000000 : ℝ)|=(1631255041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (116705223/250000000 : ℝ)*x 0 + (7042483831/10000000000 : ℝ)*x 1 + (-13/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116705223/250000000 : ℝ)^135 ≤ (36843596965877/100000000000000 : ℝ)^103 := by
    have hnat : (116705223 : ℕ)^135*100000000000000^103 ≤ 36843596965877^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116705223 250000000 36843596965877 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7042483831/10000000000 : ℝ)^135 ≤ (6315640301789/10000000000000 : ℝ)^103 := by
    have hnat : (7042483831 : ℕ)^135*10000000000000^103 ≤ 6315640301789^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7042483831 10000000000 6315640301789 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13/2000000000 : ℝ)^135 ≤ (93/5000000000000 : ℝ)^103 := by
    have hnat : (13 : ℕ)^135*5000000000000^103 ≤ 93^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13 2000000000 93 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(116705223/250000000 : ℝ), (7042483831/10000000000 : ℝ), (-13/2000000000 : ℝ)] ![(36843596965877/100000000000000 : ℝ), (6315640301789/10000000000000 : ℝ), (93/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(116705223/250000000 : ℝ)|^135 ≤ (36843596965877/100000000000000 : ℝ)^103
        have hw : |(116705223/250000000 : ℝ)|=(116705223/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7042483831/10000000000 : ℝ)|^135 ≤ (6315640301789/10000000000000 : ℝ)^103
        have hw : |(7042483831/10000000000 : ℝ)|=(7042483831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13/2000000000 : ℝ)|^135 ≤ (93/5000000000000 : ℝ)^103
        have hw : |(-13/2000000000 : ℝ)|=(13/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-410125903/2500000000 : ℝ)*x 0 + (2227185293/10000000000 : ℝ)*x 1 + (-1633172583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410125903/2500000000 : ℝ)^135 ≤ (2338980591697/25000000000000 : ℝ)^103 := by
    have hnat : (410125903 : ℕ)^135*25000000000000^103 ≤ 2338980591697^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410125903 2500000000 2338980591697 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227185293/10000000000 : ℝ)^135 ≤ (1396746353679/10000000000000 : ℝ)^103 := by
    have hnat : (2227185293 : ℕ)^135*10000000000000^103 ≤ 1396746353679^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227185293 10000000000 1396746353679 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1633172583/2000000000 : ℝ)^135 ≤ (15335322814183/20000000000000 : ℝ)^103 := by
    have hnat : (1633172583 : ℕ)^135*20000000000000^103 ≤ 15335322814183^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633172583 2000000000 15335322814183 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410125903/2500000000 : ℝ), (2227185293/10000000000 : ℝ), (-1633172583/2000000000 : ℝ)] ![(2338980591697/25000000000000 : ℝ), (1396746353679/10000000000000 : ℝ), (15335322814183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410125903/2500000000 : ℝ)|^135 ≤ (2338980591697/25000000000000 : ℝ)^103
        have hw : |(-410125903/2500000000 : ℝ)|=(410125903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2227185293/10000000000 : ℝ)|^135 ≤ (1396746353679/10000000000000 : ℝ)^103
        have hw : |(2227185293/10000000000 : ℝ)|=(2227185293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1633172583/2000000000 : ℝ)|^135 ≤ (15335322814183/20000000000000 : ℝ)^103
        have hw : |(-1633172583/2000000000 : ℝ)|=(1633172583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1787837687/10000000000 : ℝ)*x 0 + (-1039349997/5000000000 : ℝ)*x 1 + (-1634656103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1787837687/10000000000 : ℝ)^135 ≤ (654518137431/6250000000000 : ℝ)^103 := by
    have hnat : (1787837687 : ℕ)^135*6250000000000^103 ≤ 654518137431^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787837687 10000000000 654518137431 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039349997/5000000000 : ℝ)^135 ≤ (2551958669347/20000000000000 : ℝ)^103 := by
    have hnat : (1039349997 : ℕ)^135*20000000000000^103 ≤ 2551958669347^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039349997 5000000000 2551958669347 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1634656103/2000000000 : ℝ)^135 ≤ (76767916442793/100000000000000 : ℝ)^103 := by
    have hnat : (1634656103 : ℕ)^135*100000000000000^103 ≤ 76767916442793^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634656103 2000000000 76767916442793 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1787837687/10000000000 : ℝ), (-1039349997/5000000000 : ℝ), (-1634656103/2000000000 : ℝ)] ![(654518137431/6250000000000 : ℝ), (2551958669347/20000000000000 : ℝ), (76767916442793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1787837687/10000000000 : ℝ)|^135 ≤ (654518137431/6250000000000 : ℝ)^103
        have hw : |(1787837687/10000000000 : ℝ)|=(1787837687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039349997/5000000000 : ℝ)|^135 ≤ (2551958669347/20000000000000 : ℝ)^103
        have hw : |(-1039349997/5000000000 : ℝ)|=(1039349997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1634656103/2000000000 : ℝ)|^135 ≤ (76767916442793/100000000000000 : ℝ)^103
        have hw : |(-1634656103/2000000000 : ℝ)|=(1634656103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6490641347/10000000000 : ℝ)*x 0 + (845915517/2000000000 : ℝ)*x 1 + (920070911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6490641347/10000000000 : ℝ)^135 ≤ (56750435705603/100000000000000 : ℝ)^103 := by
    have hnat : (6490641347 : ℕ)^135*100000000000000^103 ≤ 56750435705603^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6490641347 10000000000 56750435705603 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845915517/2000000000 : ℝ)^135 ≤ (16186952636083/50000000000000 : ℝ)^103 := by
    have hnat : (845915517 : ℕ)^135*50000000000000^103 ≤ 16186952636083^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845915517 2000000000 16186952636083 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920070911/5000000000 : ℝ)^135 ≤ (5437829499281/50000000000000 : ℝ)^103 := by
    have hnat : (920070911 : ℕ)^135*50000000000000^103 ≤ 5437829499281^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920070911 5000000000 5437829499281 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6490641347/10000000000 : ℝ), (845915517/2000000000 : ℝ), (920070911/5000000000 : ℝ)] ![(56750435705603/100000000000000 : ℝ), (16186952636083/50000000000000 : ℝ), (5437829499281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6490641347/10000000000 : ℝ)|^135 ≤ (56750435705603/100000000000000 : ℝ)^103
        have hw : |(6490641347/10000000000 : ℝ)|=(6490641347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845915517/2000000000 : ℝ)|^135 ≤ (16186952636083/50000000000000 : ℝ)^103
        have hw : |(845915517/2000000000 : ℝ)|=(845915517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920070911/5000000000 : ℝ)|^135 ≤ (5437829499281/50000000000000 : ℝ)^103
        have hw : |(920070911/5000000000 : ℝ)|=(920070911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4311537481/5000000000 : ℝ)*x 0 + (332788381/1250000000 : ℝ)*x 1 + (-1363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311537481/5000000000 : ℝ)^135 ≤ (16470383159277/20000000000000 : ℝ)^103 := by
    have hnat : (4311537481 : ℕ)^135*20000000000000^103 ≤ 16470383159277^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311537481 5000000000 16470383159277 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332788381/1250000000 : ℝ)^135 ≤ (17648084096779/100000000000000 : ℝ)^103 := by
    have hnat : (332788381 : ℕ)^135*100000000000000^103 ≤ 17648084096779^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332788381 1250000000 17648084096779 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363/10000000000 : ℝ)^135 ≤ (49/48828125000 : ℝ)^103 := by
    have hnat : (1363 : ℕ)^135*48828125000^103 ≤ 49^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363 10000000000 49 48828125000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311537481/5000000000 : ℝ), (332788381/1250000000 : ℝ), (-1363/10000000000 : ℝ)] ![(16470383159277/20000000000000 : ℝ), (17648084096779/100000000000000 : ℝ), (49/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311537481/5000000000 : ℝ)|^135 ≤ (16470383159277/20000000000000 : ℝ)^103
        have hw : |(4311537481/5000000000 : ℝ)|=(4311537481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(332788381/1250000000 : ℝ)|^135 ≤ (17648084096779/100000000000000 : ℝ)^103
        have hw : |(332788381/1250000000 : ℝ)|=(332788381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1363/10000000000 : ℝ)|^135 ≤ (49/48828125000 : ℝ)^103
        have hw : |(-1363/10000000000 : ℝ)|=(1363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1225076297/10000000000 : ℝ)*x 0 + (5457772379/10000000000 : ℝ)*x 1 + (-574853161/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1225076297/10000000000 : ℝ)^135 ≤ (6380783579841/100000000000000 : ℝ)^103 := by
    have hnat : (1225076297 : ℕ)^135*100000000000000^103 ≤ 6380783579841^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225076297 10000000000 6380783579841 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457772379/10000000000 : ℝ)^135 ≤ (4521801271433/10000000000000 : ℝ)^103 := by
    have hnat : (5457772379 : ℕ)^135*10000000000000^103 ≤ 4521801271433^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457772379 10000000000 4521801271433 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574853161/1000000000 : ℝ)^135 ≤ (12100300922773/25000000000000 : ℝ)^103 := by
    have hnat : (574853161 : ℕ)^135*25000000000000^103 ≤ 12100300922773^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574853161 1000000000 12100300922773 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1225076297/10000000000 : ℝ), (5457772379/10000000000 : ℝ), (-574853161/1000000000 : ℝ)] ![(6380783579841/100000000000000 : ℝ), (4521801271433/10000000000000 : ℝ), (12100300922773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1225076297/10000000000 : ℝ)|^135 ≤ (6380783579841/100000000000000 : ℝ)^103
        have hw : |(-1225076297/10000000000 : ℝ)|=(1225076297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457772379/10000000000 : ℝ)|^135 ≤ (4521801271433/10000000000000 : ℝ)^103
        have hw : |(5457772379/10000000000 : ℝ)|=(5457772379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-574853161/1000000000 : ℝ)|^135 ≤ (12100300922773/25000000000000 : ℝ)^103
        have hw : |(-574853161/1000000000 : ℝ)|=(574853161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (267122711/400000000 : ℝ)*x 0 + (-573360873/5000000000 : ℝ)*x 1 + (-4512456753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267122711/400000000 : ℝ)^135 ≤ (3681742622731/6250000000000 : ℝ)^103 := by
    have hnat : (267122711 : ℕ)^135*6250000000000^103 ≤ 3681742622731^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267122711 400000000 3681742622731 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (573360873/5000000000 : ℝ)^135 ≤ (2925639725883/50000000000000 : ℝ)^103 := by
    have hnat : (573360873 : ℕ)^135*50000000000000^103 ≤ 2925639725883^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573360873 5000000000 2925639725883 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512456753/10000000000 : ℝ)^135 ≤ (352408385729/1000000000000 : ℝ)^103 := by
    have hnat : (4512456753 : ℕ)^135*1000000000000^103 ≤ 352408385729^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512456753 10000000000 352408385729 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267122711/400000000 : ℝ), (-573360873/5000000000 : ℝ), (-4512456753/10000000000 : ℝ)] ![(3681742622731/6250000000000 : ℝ), (2925639725883/50000000000000 : ℝ), (352408385729/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267122711/400000000 : ℝ)|^135 ≤ (3681742622731/6250000000000 : ℝ)^103
        have hw : |(267122711/400000000 : ℝ)|=(267122711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-573360873/5000000000 : ℝ)|^135 ≤ (2925639725883/50000000000000 : ℝ)^103
        have hw : |(-573360873/5000000000 : ℝ)|=(573360873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4512456753/10000000000 : ℝ)|^135 ≤ (352408385729/1000000000000 : ℝ)^103
        have hw : |(-4512456753/10000000000 : ℝ)|=(4512456753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (631235263/2500000000 : ℝ)*x 0 + (389089557/500000000 : ℝ)*x 1 + (385339739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (631235263/2500000000 : ℝ)^135 ≤ (3292857126173/20000000000000 : ℝ)^103 := by
    have hnat : (631235263 : ℕ)^135*20000000000000^103 ≤ 3292857126173^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631235263 2500000000 3292857126173 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389089557/500000000 : ℝ)^135 ≤ (71984702404949/100000000000000 : ℝ)^103 := by
    have hnat : (389089557 : ℕ)^135*100000000000000^103 ≤ 71984702404949^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389089557 500000000 71984702404949 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385339739/2000000000 : ℝ)^135 ≤ (2887752988833/25000000000000 : ℝ)^103 := by
    have hnat : (385339739 : ℕ)^135*25000000000000^103 ≤ 2887752988833^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385339739 2000000000 2887752988833 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(631235263/2500000000 : ℝ), (389089557/500000000 : ℝ), (385339739/2000000000 : ℝ)] ![(3292857126173/20000000000000 : ℝ), (71984702404949/100000000000000 : ℝ), (2887752988833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(631235263/2500000000 : ℝ)|^135 ≤ (3292857126173/20000000000000 : ℝ)^103
        have hw : |(631235263/2500000000 : ℝ)|=(631235263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(389089557/500000000 : ℝ)|^135 ≤ (71984702404949/100000000000000 : ℝ)^103
        have hw : |(389089557/500000000 : ℝ)|=(389089557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385339739/2000000000 : ℝ)|^135 ≤ (2887752988833/25000000000000 : ℝ)^103
        have hw : |(385339739/2000000000 : ℝ)|=(385339739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s2_s2_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4548644391/5000000000 : ℝ)*x 0 + (1937230231/10000000000 : ℝ)*x 1 + (-9819567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4548644391/5000000000 : ℝ)^135 ≤ (2760557470953/3125000000000 : ℝ)^103 := by
    have hnat : (4548644391 : ℕ)^135*3125000000000^103 ≤ 2760557470953^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548644391 5000000000 2760557470953 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1937230231/10000000000 : ℝ)^135 ≤ (11633837182059/100000000000000 : ℝ)^103 := by
    have hnat : (1937230231 : ℕ)^135*100000000000000^103 ≤ 11633837182059^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937230231 10000000000 11633837182059 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9819567/5000000000 : ℝ)^135 ≤ (2832374209/10000000000000 : ℝ)^103 := by
    have hnat : (9819567 : ℕ)^135*10000000000000^103 ≤ 2832374209^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9819567 5000000000 2832374209 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4548644391/5000000000 : ℝ), (1937230231/10000000000 : ℝ), (-9819567/5000000000 : ℝ)] ![(2760557470953/3125000000000 : ℝ), (11633837182059/100000000000000 : ℝ), (2832374209/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4548644391/5000000000 : ℝ)|^135 ≤ (2760557470953/3125000000000 : ℝ)^103
        have hw : |(4548644391/5000000000 : ℝ)|=(4548644391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1937230231/10000000000 : ℝ)|^135 ≤ (11633837182059/100000000000000 : ℝ)^103
        have hw : |(1937230231/10000000000 : ℝ)|=(1937230231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9819567/5000000000 : ℝ)|^135 ≤ (2832374209/10000000000000 : ℝ)^103
        have hw : |(-9819567/5000000000 : ℝ)|=(9819567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306060_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((89009/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89009/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44719/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44719/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40361/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40361/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4967/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4967/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-69243/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-69243/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (89009/100000 : ℝ) ^ (67/16 : ℝ) ≤ (1228243694878945903/2000000000000000000 : ℝ) := by
    have hpowers : (89009/100000 : ℝ)^67 ≤ (1228243694878945903/2000000000000000000 : ℝ)^16 := by
      have hnat : (89009 : ℕ)^67*2000000000000000000^16 ≤ 1228243694878945903^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89009 100000 1228243694878945903 2000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89009/100000 : ℝ)) (X := (1228243694878945903/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (3228243694878945903/2000000000000000000 : ℝ) ≤ (11211311868138863/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3228243694878945903/2000000000000000000 : ℝ)^16 ≤ (11211311868138863/10000000000000000 : ℝ)^67 := by
      have hnat : (3228243694878945903 : ℕ)^16*10000000000000000^67 ≤ 11211311868138863^67*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3228243694878945903 2000000000000000000 11211311868138863 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11211311868138863/10000000000000000 : ℝ)) (X := (3228243694878945903/2000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (2228243694878945903/1000000000000000000 : ℝ) ≤ (12108645560333473/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2228243694878945903/1000000000000000000 : ℝ)^16 ≤ (12108645560333473/10000000000000000 : ℝ)^67 := by
      have hnat : (2228243694878945903 : ℕ)^16*10000000000000000^67 ≤ 12108645560333473^67*1000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2228243694878945903 1000000000000000000 12108645560333473 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12108645560333473/10000000000000000 : ℝ)) (X := (2228243694878945903/1000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1211311868138863/8900900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(89733369219461/890090000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (89009/100000 : ℝ)) (alpha := (1211311868138863/8900900000000000 : ℝ)) (beta := (89733369219461/890090000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (89009/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1211311868138863/8900900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(89733369219461/890090000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (44719/50000 : ℝ) ^ (67/16 : ℝ) ≤ (2506447989973093841/4000000000000000000 : ℝ) := by
    have hpowers : (44719/50000 : ℝ)^67 ≤ (2506447989973093841/4000000000000000000 : ℝ)^16 := by
      have hnat : (44719 : ℕ)^67*4000000000000000000^16 ≤ 2506447989973093841^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44719 50000 2506447989973093841 4000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44719/50000 : ℝ)) (X := (2506447989973093841/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (6506447989973093841/4000000000000000000 : ℝ) ≤ (5615984210105943/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (6506447989973093841/4000000000000000000 : ℝ)^16 ≤ (5615984210105943/5000000000000000 : ℝ)^67 := by
      have hnat : (6506447989973093841 : ℕ)^16*5000000000000000^67 ≤ 5615984210105943^67*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6506447989973093841 4000000000000000000 5615984210105943 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5615984210105943/5000000000000000 : ℝ)) (X := (6506447989973093841/4000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (4506447989973093841/2000000000000000000 : ℝ) ≤ (2428185072463507/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (4506447989973093841/2000000000000000000 : ℝ)^16 ≤ (2428185072463507/2000000000000000 : ℝ)^67 := by
      have hnat : (4506447989973093841 : ℕ)^16*2000000000000000^67 ≤ 2428185072463507^67*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4506447989973093841 2000000000000000000 2428185072463507 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2428185072463507/2000000000000000 : ℝ)) (X := (4506447989973093841/2000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(615984210105943/4471900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(908956942105649/8943800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (44719/50000 : ℝ)) (alpha := (615984210105943/4471900000000000 : ℝ)) (beta := (908956942105649/8943800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (44719/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(615984210105943/4471900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(908956942105649/8943800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (40361/50000 : ℝ) ^ (67/16 : ℝ) ≤ (1019691142702092303/2500000000000000000 : ℝ) := by
    have hpowers : (40361/50000 : ℝ)^67 ≤ (1019691142702092303/2500000000000000000 : ℝ)^16 := by
      have hnat : (40361 : ℕ)^67*2500000000000000000^16 ≤ 1019691142702092303^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40361 50000 1019691142702092303 2500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40361/50000 : ℝ)) (X := (1019691142702092303/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (3519691142702092303/2500000000000000000 : ℝ) ≤ (542560415490791/500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3519691142702092303/2500000000000000000 : ℝ)^16 ≤ (542560415490791/500000000000000 : ℝ)^67 := by
      have hnat : (3519691142702092303 : ℕ)^16*500000000000000^67 ≤ 542560415490791^67*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519691142702092303 2500000000000000000 542560415490791 500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (542560415490791/500000000000000 : ℝ)) (X := (3519691142702092303/2500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (2269691142702092303/1250000000000000000 : ℝ) ≤ (144136612642271/125000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2269691142702092303/1250000000000000000 : ℝ)^16 ≤ (144136612642271/125000000000000 : ℝ)^67 := by
      have hnat : (2269691142702092303 : ℕ)^16*125000000000000^67 ≤ 144136612642271^67*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269691142702092303 1250000000000000000 144136612642271 125000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (144136612642271/125000000000000 : ℝ)) (X := (2269691142702092303/1250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(42560415490791/403610000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(33986035078293/403610000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (40361/50000 : ℝ)) (alpha := (42560415490791/403610000000000 : ℝ)) (beta := (33986035078293/403610000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (40361/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(42560415490791/403610000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(33986035078293/403610000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-832008397/5000000000 : ℝ)*X 0 0+(4542568797/10000000000 : ℝ)*X 0 1+(-1582542057/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4533780603/10000000000 : ℝ)*X 1 0+(-1667135821/10000000000 : ℝ)*X 1 1+(-6336032301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1576043529/10000000000 : ℝ)*X 0 0+(100614083/400000000 : ℝ)*X 0 1+(-8008075907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((718941143/2500000000 : ℝ)*X 1 0+(-557880797/5000000000 : ℝ)*X 1 1+(-4007674597/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((357472911/1250000000 : ℝ)*X 2 0+(7727724103/10000000000 : ℝ)*X 2 1+(1631255041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((116705223/250000000 : ℝ)*X 0 0+(7042483831/10000000000 : ℝ)*X 0 1+(-13/2000000000 : ℝ)*X 0 2+(116705223/250000000 : ℝ)*X 1 0+(7042483831/10000000000 : ℝ)*X 1 1+(-13/2000000000 : ℝ)*X 1 2+(116705223/250000000 : ℝ)*X 2 0+(7042483831/10000000000 : ℝ)*X 2 1+(-13/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-410125903/2500000000 : ℝ)*X 0 0+(2227185293/10000000000 : ℝ)*X 0 1+(-1633172583/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1787837687/10000000000 : ℝ)*X 1 0+(-1039349997/5000000000 : ℝ)*X 1 1+(-1634656103/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6490641347/10000000000 : ℝ)*X 2 0+(845915517/2000000000 : ℝ)*X 2 1+(920070911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((4311537481/5000000000 : ℝ)*X 0 0+(332788381/1250000000 : ℝ)*X 0 1+(-1363/10000000000 : ℝ)*X 0 2+(4311537481/5000000000 : ℝ)*X 1 0+(332788381/1250000000 : ℝ)*X 1 1+(-1363/10000000000 : ℝ)*X 1 2+(4311537481/5000000000 : ℝ)*X 2 0+(332788381/1250000000 : ℝ)*X 2 1+(-1363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1225076297/10000000000 : ℝ)*X 0 0+(5457772379/10000000000 : ℝ)*X 0 1+(-574853161/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((267122711/400000000 : ℝ)*X 1 0+(-573360873/5000000000 : ℝ)*X 1 1+(-4512456753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((631235263/2500000000 : ℝ)*X 2 0+(389089557/500000000 : ℝ)*X 2 1+(385339739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4548644391/5000000000 : ℝ)*X 0 0+(1937230231/10000000000 : ℝ)*X 0 1+(-9819567/5000000000 : ℝ)*X 0 2+(4548644391/5000000000 : ℝ)*X 1 0+(1937230231/10000000000 : ℝ)*X 1 1+(-9819567/5000000000 : ℝ)*X 1 2+(4548644391/5000000000 : ℝ)*X 2 0+(1937230231/10000000000 : ℝ)*X 2 1+(-9819567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((4967/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4967/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (120462393468305067504329502994857/16065266088303100000000000000000000000 : ℝ) := by norm_num
    linear_combination (261082581953/1000000000000 : ℝ)*(base5) + (162228654193/200000000000 : ℝ)*(base7) + (11113/62500000000 : ℝ)*(base39) + (788133/1000000000000 : ℝ)*(base43) + (2190291919769/1000000000000 : ℝ)*(major_s2_0) + (438058226327/200000000000 : ℝ)*(major_s2_1) + (2190291919769/1000000000000 : ℝ)*(major_s2_2) + (2048757/1000000000000 : ℝ)*(sp_s2_0) + (4167579/500000000000 : ℝ)*(sp_s2_1) + (491426829807/200000000000 : ℝ)*(sp_s2_7) + (2457106680207/1000000000000 : ℝ)*(sp_s2_8) + (543643755949/200000000000 : ℝ)*(sp_s2_9) + (1970612438047/1000000000000 : ℝ)*(sp_s2_13) + (21970561/1000000000000 : ℝ)*(sp_s2_15) + (355137937259/250000000000 : ℝ)*(f.failure) + (98285479437/40000000000 : ℝ)*(f.sum) + (4200936184402020817/36098071180000000000000000000000 : ℝ)*base63 + (14502542791161/50451250000000000000000000 : ℝ)*base64 + (780590745003881/1788760000000000000000000000 : ℝ)*base66 + (62205976235977/201805000000000000000000000 : ℝ)*base69 + (131814176559876357007/359249224900000000000000000000000 : ℝ)*base71 + (32383300281683/890090000000000000000000000 : ℝ)*base73 + (499826724370961/894380000000000000000000000 : ℝ)*base75 + (801113424941367/8900900000000000000000000000 : ℝ)*base77 + (31009099621266257269/159215738840000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (4413/12500000000000000 : ℝ)*base86 + (8087/12500000000000000 : ℝ)*base89 + (4413/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/2500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (212196373437601691075391487314987/16065266088303100000000000000000000000 : ℝ) := by norm_num
    linear_combination (208881555813/250000000000 : ℝ)*(base7) + (203343/500000000000 : ℝ)*(base34) + (11079/250000000000 : ℝ)*(base39) + (1157291/1000000000000 : ℝ)*(base53) + (2061506520277/1000000000000 : ℝ)*(major_s2_0) + (2061506926963/1000000000000 : ℝ)*(major_s2_1) + (2061505769671/1000000000000 : ℝ)*(major_s2_2) + (2537627/125000000000 : ℝ)*(sp_s2_7) + (45099559/1000000000000 : ℝ)*(sp_s2_8) + (2267952026173/1000000000000 : ℝ)*(sp_s2_14) + (566981908579/250000000000 : ℝ)*(sp_s2_15) + (1133986945583/500000000000 : ℝ)*(sp_s2_16) + (2172517374319/1000000000000 : ℝ)*(sp_s2_20) + (4306789/125000000000 : ℝ)*(sp_s2_27) + (267405202413/200000000000 : ℝ)*(f.failure) + (1133986945583/500000000000 : ℝ)*(f.sum) + (13950573721074003959/180490355900000000000000000000000 : ℝ)*base63 + (47170860990461/100902500000000000000000000 : ℝ)*base65 + (5047500933638547/8943800000000000000000000000 : ℝ)*base67 + (31572487692661/403610000000000000000000000 : ℝ)*base68 + (43313935923278356481/359249224900000000000000000000000 : ℝ)*base71 + (50354500619801/55630625000000000000000000 : ℝ)*base73 + (210422576365051/4471900000000000000000000000 : ℝ)*base74 + (2800446206720591/8900900000000000000000000000 : ℝ)*base77 + (64873525805111633003/796078694200000000000000000000000 : ℝ)*base79 + (4591/10000000000000000 : ℝ)*base86 + (4591/10000000000000000 : ℝ)*base88 + (5409/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-69243/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-69243/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (604430186050294462778794767/398039347100000000000000000000000 : ℝ) := by norm_num
    linear_combination (113775963571/200000000000 : ℝ)*(base7) + (638179/1000000000000 : ℝ)*(base16) + (14883/12500000000 : ℝ)*(base34) + (106787/200000000000 : ℝ)*(base40) + (395855691031/1000000000000 : ℝ)*(base43) + (927495866603/500000000000 : ℝ)*(major_s2_0) + (291827446563/200000000000 : ℝ)*(major_s2_1) + (370998584769/200000000000 : ℝ)*(major_s2_2) + (4513839/250000000000 : ℝ)*(sp_s2_9) + (74263/5000000000 : ℝ)*(sp_s2_20) + (175834657077/100000000000 : ℝ)*(sp_s2_21) + (2154202814261/1000000000000 : ℝ)*(sp_s2_22) + (879164853027/500000000000 : ℝ)*(sp_s2_23) + (177195155421/100000000000 : ℝ)*(sp_s2_27) + (601543889797/500000000000 : ℝ)*(f.failure) + (53855086311/25000000000 : ℝ)*(f.sum) + (949379996486670981/36098071180000000000000000000000 : ℝ)*base62 + (493628274431/3228880000000000000000000 : ℝ)*base65 + (1177239566627027/1788760000000000000000000000 : ℝ)*base67 + (531281992857/807220000000000000000000 : ℝ)*base69 + (8952727505922866469/44906153112500000000000000000000 : ℝ)*base70 + (586665125541223/890090000000000000000000000 : ℝ)*base73 + (307407648512781/894380000000000000000000000 : ℝ)*base75 + (1408246916771821/4450450000000000000000000000 : ℝ)*base76 + (2369895480934816651/6368629553600000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (29879/25000000000000000 : ℝ)*base86 + (29879/25000000000000000 : ℝ)*base88 + (4879/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((89009/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89009/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44719/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44719/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40361/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40361/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4967/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4967/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-69243/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-69243/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306060_s2 p hpa hpb X hX hprev1

#print axioms solution
