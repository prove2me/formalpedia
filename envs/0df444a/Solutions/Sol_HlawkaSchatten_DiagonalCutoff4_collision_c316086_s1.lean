-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:08:35.299871+00:00
-- url     : https://prove2.me/submissions/83163d64-4ec8-4de4-8c9f-30d2d689101c

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
theorem collision_support_c316086_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-226268789/5000000000 : ℝ)*x 0 + (-748901717/1250000000 : ℝ)*x 1 + (5369291429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226268789/5000000000 : ℝ)^77 ≤ (2009275431437/100000000000000 : ℝ)^61 := by
    have hnat : (226268789 : ℕ)^77*100000000000000^61 ≤ 2009275431437^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226268789 5000000000 2009275431437 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748901717/1250000000 : ℝ)^77 ≤ (6547387666971/12500000000000 : ℝ)^61 := by
    have hnat : (748901717 : ℕ)^77*12500000000000^61 ≤ 6547387666971^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748901717 1250000000 6547387666971 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5369291429/10000000000 : ℝ)^77 ≤ (45611623216621/100000000000000 : ℝ)^61 := by
    have hnat : (5369291429 : ℕ)^77*100000000000000^61 ≤ 45611623216621^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369291429 10000000000 45611623216621 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226268789/5000000000 : ℝ), (-748901717/1250000000 : ℝ), (5369291429/10000000000 : ℝ)] ![(2009275431437/100000000000000 : ℝ), (6547387666971/12500000000000 : ℝ), (45611623216621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226268789/5000000000 : ℝ)|^77 ≤ (2009275431437/100000000000000 : ℝ)^61
        have hw : |(-226268789/5000000000 : ℝ)|=(226268789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-748901717/1250000000 : ℝ)|^77 ≤ (6547387666971/12500000000000 : ℝ)^61
        have hw : |(-748901717/1250000000 : ℝ)|=(748901717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5369291429/10000000000 : ℝ)|^77 ≤ (45611623216621/100000000000000 : ℝ)^61
        have hw : |(5369291429/10000000000 : ℝ)|=(5369291429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3017282481/5000000000 : ℝ)*x 0 + (3250713827/10000000000 : ℝ)*x 1 + (3114265599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3017282481/5000000000 : ℝ)^77 ≤ (52857970315589/100000000000000 : ℝ)^61 := by
    have hnat : (3017282481 : ℕ)^77*100000000000000^61 ≤ 52857970315589^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017282481 5000000000 52857970315589 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3250713827/10000000000 : ℝ)^77 ≤ (12104397191367/50000000000000 : ℝ)^61 := by
    have hnat : (3250713827 : ℕ)^77*50000000000000^61 ≤ 12104397191367^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3250713827 10000000000 12104397191367 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3114265599/10000000000 : ℝ)^77 ≤ (2293323528479/10000000000000 : ℝ)^61 := by
    have hnat : (3114265599 : ℕ)^77*10000000000000^61 ≤ 2293323528479^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3114265599 10000000000 2293323528479 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3017282481/5000000000 : ℝ), (3250713827/10000000000 : ℝ), (3114265599/10000000000 : ℝ)] ![(52857970315589/100000000000000 : ℝ), (12104397191367/50000000000000 : ℝ), (2293323528479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3017282481/5000000000 : ℝ)|^77 ≤ (52857970315589/100000000000000 : ℝ)^61
        have hw : |(3017282481/5000000000 : ℝ)|=(3017282481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3250713827/10000000000 : ℝ)|^77 ≤ (12104397191367/50000000000000 : ℝ)^61
        have hw : |(3250713827/10000000000 : ℝ)|=(3250713827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3114265599/10000000000 : ℝ)|^77 ≤ (2293323528479/10000000000000 : ℝ)^61
        have hw : |(3114265599/10000000000 : ℝ)|=(3114265599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (71566631/125000000 : ℝ)*x 0 + (-861403869/2500000000 : ℝ)*x 1 + (-3279814851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71566631/125000000 : ℝ)^77 ≤ (49462132712127/100000000000000 : ℝ)^61 := by
    have hnat : (71566631 : ℕ)^77*100000000000000^61 ≤ 49462132712127^61*125000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71566631 125000000 49462132712127 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861403869/2500000000 : ℝ)^77 ≤ (26055185485663/100000000000000 : ℝ)^61 := by
    have hnat : (861403869 : ℕ)^77*100000000000000^61 ≤ 26055185485663^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861403869 2500000000 26055185485663 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3279814851/10000000000 : ℝ)^77 ≤ (306033522303/1250000000000 : ℝ)^61 := by
    have hnat : (3279814851 : ℕ)^77*1250000000000^61 ≤ 306033522303^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3279814851 10000000000 306033522303 1250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(71566631/125000000 : ℝ), (-861403869/2500000000 : ℝ), (-3279814851/10000000000 : ℝ)] ![(49462132712127/100000000000000 : ℝ), (26055185485663/100000000000000 : ℝ), (306033522303/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(71566631/125000000 : ℝ)|^77 ≤ (49462132712127/100000000000000 : ℝ)^61
        have hw : |(71566631/125000000 : ℝ)|=(71566631/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-861403869/2500000000 : ℝ)|^77 ≤ (26055185485663/100000000000000 : ℝ)^61
        have hw : |(-861403869/2500000000 : ℝ)|=(861403869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3279814851/10000000000 : ℝ)|^77 ≤ (306033522303/1250000000000 : ℝ)^61
        have hw : |(-3279814851/10000000000 : ℝ)|=(3279814851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-235695003/10000000000 : ℝ)*x 0 + (-6823238783/10000000000 : ℝ)*x 1 + (4587543977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235695003/10000000000 : ℝ)^77 ≤ (13779895031/1562500000000 : ℝ)^61 := by
    have hnat : (235695003 : ℕ)^77*1562500000000^61 ≤ 13779895031^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235695003 10000000000 13779895031 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6823238783/10000000000 : ℝ)^77 ≤ (61723012277909/100000000000000 : ℝ)^61 := by
    have hnat : (6823238783 : ℕ)^77*100000000000000^61 ≤ 61723012277909^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6823238783 10000000000 61723012277909 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4587543977/10000000000 : ℝ)^77 ≤ (37395074428267/100000000000000 : ℝ)^61 := by
    have hnat : (4587543977 : ℕ)^77*100000000000000^61 ≤ 37395074428267^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4587543977 10000000000 37395074428267 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235695003/10000000000 : ℝ), (-6823238783/10000000000 : ℝ), (4587543977/10000000000 : ℝ)] ![(13779895031/1562500000000 : ℝ), (61723012277909/100000000000000 : ℝ), (37395074428267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235695003/10000000000 : ℝ)|^77 ≤ (13779895031/1562500000000 : ℝ)^61
        have hw : |(-235695003/10000000000 : ℝ)|=(235695003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6823238783/10000000000 : ℝ)|^77 ≤ (61723012277909/100000000000000 : ℝ)^61
        have hw : |(-6823238783/10000000000 : ℝ)|=(6823238783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4587543977/10000000000 : ℝ)|^77 ≤ (37395074428267/100000000000000 : ℝ)^61
        have hw : |(4587543977/10000000000 : ℝ)|=(4587543977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5847139/9765625 : ℝ)*x 0 + (4035013/12500000 : ℝ)*x 1 + (1596453149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5847139/9765625 : ℝ)^77 ≤ (26168896639671/50000000000000 : ℝ)^61 := by
    have hnat : (5847139 : ℕ)^77*50000000000000^61 ≤ 26168896639671^61*9765625^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847139 9765625 26168896639671 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4035013/12500000 : ℝ)^77 ≤ (11997782249643/50000000000000 : ℝ)^61 := by
    have hnat : (4035013 : ℕ)^77*50000000000000^61 ≤ 11997782249643^61*12500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035013 12500000 11997782249643 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596453149/5000000000 : ℝ)^77 ≤ (4733328442551/20000000000000 : ℝ)^61 := by
    have hnat : (1596453149 : ℕ)^77*20000000000000^61 ≤ 4733328442551^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596453149 5000000000 4733328442551 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5847139/9765625 : ℝ), (4035013/12500000 : ℝ), (1596453149/5000000000 : ℝ)] ![(26168896639671/50000000000000 : ℝ), (11997782249643/50000000000000 : ℝ), (4733328442551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5847139/9765625 : ℝ)|^77 ≤ (26168896639671/50000000000000 : ℝ)^61
        have hw : |(5847139/9765625 : ℝ)|=(5847139/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4035013/12500000 : ℝ)|^77 ≤ (11997782249643/50000000000000 : ℝ)^61
        have hw : |(4035013/12500000 : ℝ)|=(4035013/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596453149/5000000000 : ℝ)|^77 ≤ (4733328442551/20000000000000 : ℝ)^61
        have hw : |(1596453149/5000000000 : ℝ)|=(1596453149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1177920487/2000000000 : ℝ)*x 0 + (-1647836333/5000000000 : ℝ)*x 1 + (-64798801/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1177920487/2000000000 : ℝ)^77 ≤ (800941300957/1562500000000 : ℝ)^61 := by
    have hnat : (1177920487 : ℕ)^77*1562500000000^61 ≤ 800941300957^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177920487 2000000000 800941300957 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1647836333/5000000000 : ℝ)^77 ≤ (24632198196397/100000000000000 : ℝ)^61 := by
    have hnat : (1647836333 : ℕ)^77*100000000000000^61 ≤ 24632198196397^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1647836333 5000000000 24632198196397 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64798801/200000000 : ℝ)^77 ≤ (12053779266793/50000000000000 : ℝ)^61 := by
    have hnat : (64798801 : ℕ)^77*50000000000000^61 ≤ 12053779266793^61*200000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64798801 200000000 12053779266793 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1177920487/2000000000 : ℝ), (-1647836333/5000000000 : ℝ), (-64798801/200000000 : ℝ)] ![(800941300957/1562500000000 : ℝ), (24632198196397/100000000000000 : ℝ), (12053779266793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1177920487/2000000000 : ℝ)|^77 ≤ (800941300957/1562500000000 : ℝ)^61
        have hw : |(1177920487/2000000000 : ℝ)|=(1177920487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1647836333/5000000000 : ℝ)|^77 ≤ (24632198196397/100000000000000 : ℝ)^61
        have hw : |(-1647836333/5000000000 : ℝ)|=(1647836333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64798801/200000000 : ℝ)|^77 ≤ (12053779266793/50000000000000 : ℝ)^61
        have hw : |(-64798801/200000000 : ℝ)|=(64798801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3079012661/10000000000 : ℝ)*x 0 + (-1481615759/10000000000 : ℝ)*x 1 + (925371053/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3079012661/10000000000 : ℝ)^77 ≤ (22606031091263/100000000000000 : ℝ)^61 := by
    have hnat : (3079012661 : ℕ)^77*100000000000000^61 ≤ 22606031091263^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3079012661 10000000000 22606031091263 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1481615759/10000000000 : ℝ)^77 ≤ (4489454932791/50000000000000 : ℝ)^61 := by
    have hnat : (1481615759 : ℕ)^77*50000000000000^61 ≤ 4489454932791^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481615759 10000000000 4489454932791 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925371053/1250000000 : ℝ)^77 ≤ (8551882378989/12500000000000 : ℝ)^61 := by
    have hnat : (925371053 : ℕ)^77*12500000000000^61 ≤ 8551882378989^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925371053 1250000000 8551882378989 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3079012661/10000000000 : ℝ), (-1481615759/10000000000 : ℝ), (925371053/1250000000 : ℝ)] ![(22606031091263/100000000000000 : ℝ), (4489454932791/50000000000000 : ℝ), (8551882378989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3079012661/10000000000 : ℝ)|^77 ≤ (22606031091263/100000000000000 : ℝ)^61
        have hw : |(3079012661/10000000000 : ℝ)|=(3079012661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1481615759/10000000000 : ℝ)|^77 ≤ (4489454932791/50000000000000 : ℝ)^61
        have hw : |(-1481615759/10000000000 : ℝ)|=(1481615759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(925371053/1250000000 : ℝ)|^77 ≤ (8551882378989/12500000000000 : ℝ)^61
        have hw : |(925371053/1250000000 : ℝ)|=(925371053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-10429623/10000000000 : ℝ)*x 0 + (-5789744903/10000000000 : ℝ)*x 1 + (359866361/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10429623/10000000000 : ℝ)^77 ≤ (8612815327/50000000000000 : ℝ)^61 := by
    have hnat : (10429623 : ℕ)^77*50000000000000^61 ≤ 8612815327^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10429623 10000000000 8612815327 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5789744903/10000000000 : ℝ)^77 ≤ (10033123548983/20000000000000 : ℝ)^61 := by
    have hnat : (5789744903 : ℕ)^77*20000000000000^61 ≤ 10033123548983^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5789744903 10000000000 10033123548983 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359866361/625000000 : ℝ)^77 ≤ (24908578305741/50000000000000 : ℝ)^61 := by
    have hnat : (359866361 : ℕ)^77*50000000000000^61 ≤ 24908578305741^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359866361 625000000 24908578305741 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10429623/10000000000 : ℝ), (-5789744903/10000000000 : ℝ), (359866361/625000000 : ℝ)] ![(8612815327/50000000000000 : ℝ), (10033123548983/20000000000000 : ℝ), (24908578305741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10429623/10000000000 : ℝ)|^77 ≤ (8612815327/50000000000000 : ℝ)^61
        have hw : |(-10429623/10000000000 : ℝ)|=(10429623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5789744903/10000000000 : ℝ)|^77 ≤ (10033123548983/20000000000000 : ℝ)^61
        have hw : |(-5789744903/10000000000 : ℝ)|=(5789744903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(359866361/625000000 : ℝ)|^77 ≤ (24908578305741/50000000000000 : ℝ)^61
        have hw : |(359866361/625000000 : ℝ)|=(359866361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6515996603/10000000000 : ℝ)*x 0 + (766859667/2500000000 : ℝ)*x 1 + (84771117/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6515996603/10000000000 : ℝ)^77 ≤ (11647130364509/20000000000000 : ℝ)^61 := by
    have hnat : (6515996603 : ℕ)^77*20000000000000^61 ≤ 11647130364509^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6515996603 10000000000 11647130364509 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (766859667/2500000000 : ℝ)^77 ≤ (22498819288067/100000000000000 : ℝ)^61 := by
    have hnat : (766859667 : ℕ)^77*100000000000000^61 ≤ 22498819288067^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766859667 2500000000 22498819288067 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84771117/312500000 : ℝ)^77 ≤ (9632764435497/50000000000000 : ℝ)^61 := by
    have hnat : (84771117 : ℕ)^77*50000000000000^61 ≤ 9632764435497^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84771117 312500000 9632764435497 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6515996603/10000000000 : ℝ), (766859667/2500000000 : ℝ), (84771117/312500000 : ℝ)] ![(11647130364509/20000000000000 : ℝ), (22498819288067/100000000000000 : ℝ), (9632764435497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6515996603/10000000000 : ℝ)|^77 ≤ (11647130364509/20000000000000 : ℝ)^61
        have hw : |(6515996603/10000000000 : ℝ)|=(6515996603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(766859667/2500000000 : ℝ)|^77 ≤ (22498819288067/100000000000000 : ℝ)^61
        have hw : |(766859667/2500000000 : ℝ)|=(766859667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84771117/312500000 : ℝ)|^77 ≤ (9632764435497/50000000000000 : ℝ)^61
        have hw : |(84771117/312500000 : ℝ)|=(84771117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6126233499/10000000000 : ℝ)*x 0 + (-338009333/1000000000 : ℝ)*x 1 + (-2870949829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6126233499/10000000000 : ℝ)^77 ≤ (26936766629649/50000000000000 : ℝ)^61 := by
    have hnat : (6126233499 : ℕ)^77*50000000000000^61 ≤ 26936766629649^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6126233499 10000000000 26936766629649 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338009333/1000000000 : ℝ)^77 ≤ (3178915747359/12500000000000 : ℝ)^61 := by
    have hnat : (338009333 : ℕ)^77*12500000000000^61 ≤ 3178915747359^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338009333 1000000000 3178915747359 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2870949829/10000000000 : ℝ)^77 ≤ (20695140740407/100000000000000 : ℝ)^61 := by
    have hnat : (2870949829 : ℕ)^77*100000000000000^61 ≤ 20695140740407^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870949829 10000000000 20695140740407 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6126233499/10000000000 : ℝ), (-338009333/1000000000 : ℝ), (-2870949829/10000000000 : ℝ)] ![(26936766629649/50000000000000 : ℝ), (3178915747359/12500000000000 : ℝ), (20695140740407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6126233499/10000000000 : ℝ)|^77 ≤ (26936766629649/50000000000000 : ℝ)^61
        have hw : |(6126233499/10000000000 : ℝ)|=(6126233499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338009333/1000000000 : ℝ)|^77 ≤ (3178915747359/12500000000000 : ℝ)^61
        have hw : |(-338009333/1000000000 : ℝ)|=(338009333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2870949829/10000000000 : ℝ)|^77 ≤ (20695140740407/100000000000000 : ℝ)^61
        have hw : |(-2870949829/10000000000 : ℝ)|=(2870949829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3248609717/10000000000 : ℝ)*x 0 + (-608092033/2500000000 : ℝ)*x 1 + (6585726511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3248609717/10000000000 : ℝ)^77 ≤ (24189016177477/100000000000000 : ℝ)^61 := by
    have hnat : (3248609717 : ℕ)^77*100000000000000^61 ≤ 24189016177477^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3248609717 10000000000 24189016177477 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608092033/2500000000 : ℝ)^77 ≤ (524611531587/3125000000000 : ℝ)^61 := by
    have hnat : (608092033 : ℕ)^77*3125000000000^61 ≤ 524611531587^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608092033 2500000000 524611531587 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6585726511/10000000000 : ℝ)^77 ≤ (59023414797503/100000000000000 : ℝ)^61 := by
    have hnat : (6585726511 : ℕ)^77*100000000000000^61 ≤ 59023414797503^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6585726511 10000000000 59023414797503 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3248609717/10000000000 : ℝ), (-608092033/2500000000 : ℝ), (6585726511/10000000000 : ℝ)] ![(24189016177477/100000000000000 : ℝ), (524611531587/3125000000000 : ℝ), (59023414797503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3248609717/10000000000 : ℝ)|^77 ≤ (24189016177477/100000000000000 : ℝ)^61
        have hw : |(3248609717/10000000000 : ℝ)|=(3248609717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608092033/2500000000 : ℝ)|^77 ≤ (524611531587/3125000000000 : ℝ)^61
        have hw : |(-608092033/2500000000 : ℝ)|=(608092033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6585726511/10000000000 : ℝ)|^77 ≤ (59023414797503/100000000000000 : ℝ)^61
        have hw : |(6585726511/10000000000 : ℝ)|=(6585726511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2253403/5000000000 : ℝ)*x 0 + (-51139609/80000000 : ℝ)*x 1 + (5138287567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2253403/5000000000 : ℝ)^77 ≤ (47784287/800000000000 : ℝ)^61 := by
    have hnat : (2253403 : ℕ)^77*800000000000^61 ≤ 47784287^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253403 5000000000 47784287 800000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51139609/80000000 : ℝ)^77 ≤ (56845348745049/100000000000000 : ℝ)^61 := by
    have hnat : (51139609 : ℕ)^77*100000000000000^61 ≤ 56845348745049^61*80000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51139609 80000000 56845348745049 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138287567/10000000000 : ℝ)^77 ≤ (21574339101021/50000000000000 : ℝ)^61 := by
    have hnat : (5138287567 : ℕ)^77*50000000000000^61 ≤ 21574339101021^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138287567 10000000000 21574339101021 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2253403/5000000000 : ℝ), (-51139609/80000000 : ℝ), (5138287567/10000000000 : ℝ)] ![(47784287/800000000000 : ℝ), (56845348745049/100000000000000 : ℝ), (21574339101021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2253403/5000000000 : ℝ)|^77 ≤ (47784287/800000000000 : ℝ)^61
        have hw : |(-2253403/5000000000 : ℝ)|=(2253403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51139609/80000000 : ℝ)|^77 ≤ (56845348745049/100000000000000 : ℝ)^61
        have hw : |(-51139609/80000000 : ℝ)|=(51139609/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138287567/10000000000 : ℝ)|^77 ≤ (21574339101021/50000000000000 : ℝ)^61
        have hw : |(5138287567/10000000000 : ℝ)|=(5138287567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3260959597/5000000000 : ℝ)*x 0 + (370643119/1250000000 : ℝ)*x 1 + (2809947593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3260959597/5000000000 : ℝ)^77 ≤ (29151237912097/50000000000000 : ℝ)^61 := by
    have hnat : (3260959597 : ℕ)^77*50000000000000^61 ≤ 29151237912097^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3260959597 5000000000 29151237912097 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370643119/1250000000 : ℝ)^77 ≤ (4311180121817/20000000000000 : ℝ)^61 := by
    have hnat : (370643119 : ℕ)^77*20000000000000^61 ≤ 4311180121817^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370643119 1250000000 4311180121817 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2809947593/10000000000 : ℝ)^77 ≤ (20141623547713/100000000000000 : ℝ)^61 := by
    have hnat : (2809947593 : ℕ)^77*100000000000000^61 ≤ 20141623547713^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809947593 10000000000 20141623547713 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3260959597/5000000000 : ℝ), (370643119/1250000000 : ℝ), (2809947593/10000000000 : ℝ)] ![(29151237912097/50000000000000 : ℝ), (4311180121817/20000000000000 : ℝ), (20141623547713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3260959597/5000000000 : ℝ)|^77 ≤ (29151237912097/50000000000000 : ℝ)^61
        have hw : |(3260959597/5000000000 : ℝ)|=(3260959597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(370643119/1250000000 : ℝ)|^77 ≤ (4311180121817/20000000000000 : ℝ)^61
        have hw : |(370643119/1250000000 : ℝ)|=(370643119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2809947593/10000000000 : ℝ)|^77 ≤ (20141623547713/100000000000000 : ℝ)^61
        have hw : |(2809947593/10000000000 : ℝ)|=(2809947593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (698492687/1250000000 : ℝ)*x 0 + (-1779267089/5000000000 : ℝ)*x 1 + (-415420711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (698492687/1250000000 : ℝ)^77 ≤ (5996077906563/12500000000000 : ℝ)^61 := by
    have hnat : (698492687 : ℕ)^77*12500000000000^61 ≤ 5996077906563^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698492687 1250000000 5996077906563 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1779267089/5000000000 : ℝ)^77 ≤ (1356881036681/5000000000000 : ℝ)^61 := by
    have hnat : (1779267089 : ℕ)^77*5000000000000^61 ≤ 1356881036681^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779267089 5000000000 1356881036681 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415420711/1250000000 : ℝ)^77 ≤ (24893756005731/100000000000000 : ℝ)^61 := by
    have hnat : (415420711 : ℕ)^77*100000000000000^61 ≤ 24893756005731^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415420711 1250000000 24893756005731 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(698492687/1250000000 : ℝ), (-1779267089/5000000000 : ℝ), (-415420711/1250000000 : ℝ)] ![(5996077906563/12500000000000 : ℝ), (1356881036681/5000000000000 : ℝ), (24893756005731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(698492687/1250000000 : ℝ)|^77 ≤ (5996077906563/12500000000000 : ℝ)^61
        have hw : |(698492687/1250000000 : ℝ)|=(698492687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1779267089/5000000000 : ℝ)|^77 ≤ (1356881036681/5000000000000 : ℝ)^61
        have hw : |(-1779267089/5000000000 : ℝ)|=(1779267089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415420711/1250000000 : ℝ)|^77 ≤ (24893756005731/100000000000000 : ℝ)^61
        have hw : |(-415420711/1250000000 : ℝ)|=(415420711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316086_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4618638859/10000000000 : ℝ)*x 0 + (-1289020429/5000000000 : ℝ)*x 1 + (5238926781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4618638859/10000000000 : ℝ)^77 ≤ (754306194677/2000000000000 : ℝ)^61 := by
    have hnat : (4618638859 : ℕ)^77*2000000000000^61 ≤ 754306194677^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618638859 10000000000 754306194677 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1289020429/5000000000 : ℝ)^77 ≤ (4516624785357/25000000000000 : ℝ)^61 := by
    have hnat : (1289020429 : ℕ)^77*25000000000000^61 ≤ 4516624785357^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289020429 5000000000 4516624785357 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238926781/10000000000 : ℝ)^77 ≤ (11054547779177/25000000000000 : ℝ)^61 := by
    have hnat : (5238926781 : ℕ)^77*25000000000000^61 ≤ 11054547779177^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238926781 10000000000 11054547779177 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4618638859/10000000000 : ℝ), (-1289020429/5000000000 : ℝ), (5238926781/10000000000 : ℝ)] ![(754306194677/2000000000000 : ℝ), (4516624785357/25000000000000 : ℝ), (11054547779177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4618638859/10000000000 : ℝ)|^77 ≤ (754306194677/2000000000000 : ℝ)^61
        have hw : |(4618638859/10000000000 : ℝ)|=(4618638859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1289020429/5000000000 : ℝ)|^77 ≤ (4516624785357/25000000000000 : ℝ)^61
        have hw : |(-1289020429/5000000000 : ℝ)|=(1289020429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238926781/10000000000 : ℝ)|^77 ≤ (11054547779177/25000000000000 : ℝ)^61
        have hw : |(5238926781/10000000000 : ℝ)|=(5238926781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316086_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((13461/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13461/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3931/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3931/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78813/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(78813/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4659/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4659/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2167/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2167/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2239/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2239/6250 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (13461/20000 : ℝ) ^ (19/4 : ℝ) ≤ (15248418778180927497/100000000000000000000 : ℝ) := by
    have hpowers : (13461/20000 : ℝ)^19 ≤ (15248418778180927497/100000000000000000000 : ℝ)^4 := by
      have hnat : (13461 : ℕ)^19*100000000000000000000^4 ≤ 15248418778180927497^4*20000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13461 20000 15248418778180927497 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13461/20000 : ℝ)) (X := (15248418778180927497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (115248418778180927497/100000000000000000000 : ℝ) ≤ (5151643345478727/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (115248418778180927497/100000000000000000000 : ℝ)^4 ≤ (5151643345478727/5000000000000000 : ℝ)^19 := by
      have hnat : (115248418778180927497 : ℕ)^4*5000000000000000^19 ≤ 5151643345478727^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115248418778180927497 100000000000000000000 5151643345478727 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5151643345478727/5000000000000000 : ℝ)) (X := (115248418778180927497/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (65248418778180927497/50000000000000000000 : ℝ) ≤ (2644093740728979/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (65248418778180927497/50000000000000000000 : ℝ)^4 ≤ (2644093740728979/2500000000000000 : ℝ)^19 := by
      have hnat : (65248418778180927497 : ℕ)^4*2500000000000000^19 ≤ 2644093740728979^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65248418778180927497 50000000000000000000 2644093740728979 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2644093740728979/2500000000000000 : ℝ)) (X := (65248418778180927497/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(151643345478727/3365250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(45514711993077/1121750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (13461/20000 : ℝ)) (alpha := (151643345478727/3365250000000000 : ℝ)) (beta := (45514711993077/1121750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13461/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(151643345478727/3365250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(45514711993077/1121750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3931/5000 : ℝ) ^ (19/4 : ℝ) ≤ (31899357627363478733/100000000000000000000 : ℝ) := by
    have hpowers : (3931/5000 : ℝ)^19 ≤ (31899357627363478733/100000000000000000000 : ℝ)^4 := by
      have hnat : (3931 : ℕ)^19*100000000000000000000^4 ≤ 31899357627363478733^4*5000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3931 5000 31899357627363478733 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3931/5000 : ℝ)) (X := (31899357627363478733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (131899357627363478733/100000000000000000000 : ℝ) ≤ (5300102307708157/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (131899357627363478733/100000000000000000000 : ℝ)^4 ≤ (5300102307708157/5000000000000000 : ℝ)^19 := by
      have hnat : (131899357627363478733 : ℕ)^4*5000000000000000^19 ≤ 5300102307708157^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131899357627363478733 100000000000000000000 5300102307708157 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5300102307708157/5000000000000000 : ℝ)) (X := (131899357627363478733/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (81899357627363478733/50000000000000000000 : ℝ) ≤ (2218952439593027/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (81899357627363478733/50000000000000000000 : ℝ)^4 ≤ (2218952439593027/2000000000000000 : ℝ)^19 := by
      have hnat : (81899357627363478733 : ℕ)^4*2000000000000000^19 ≤ 2218952439593027^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81899357627363478733 50000000000000000000 2218952439593027 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2218952439593027/2000000000000000 : ℝ)) (X := (81899357627363478733/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(300102307708157/3931000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(494557582548821/7862000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (3931/5000 : ℝ)) (alpha := (300102307708157/3931000000000000 : ℝ)) (beta := (494557582548821/7862000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (3931/5000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(300102307708157/3931000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(494557582548821/7862000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (78813/100000 : ℝ) ^ (19/4 : ℝ) ≤ (32273036633475875373/100000000000000000000 : ℝ) := by
    have hpowers : (78813/100000 : ℝ)^19 ≤ (32273036633475875373/100000000000000000000 : ℝ)^4 := by
      have hnat : (78813 : ℕ)^19*100000000000000000000^4 ≤ 32273036633475875373^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78813 100000 32273036633475875373 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78813/100000 : ℝ)) (X := (32273036633475875373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (132273036633475875373/100000000000000000000 : ℝ) ≤ (10606519879679139/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (132273036633475875373/100000000000000000000 : ℝ)^4 ≤ (10606519879679139/10000000000000000 : ℝ)^19 := by
      have hnat : (132273036633475875373 : ℕ)^4*10000000000000000^19 ≤ 10606519879679139^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132273036633475875373 100000000000000000000 10606519879679139 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10606519879679139/10000000000000000 : ℝ)) (X := (132273036633475875373/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (82273036633475875373/50000000000000000000 : ℝ) ≤ (11105400243051979/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (82273036633475875373/50000000000000000000 : ℝ)^4 ≤ (11105400243051979/10000000000000000 : ℝ)^19 := by
      have hnat : (82273036633475875373 : ℕ)^4*10000000000000000^19 ≤ 11105400243051979^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82273036633475875373 50000000000000000000 11105400243051979 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11105400243051979/10000000000000000 : ℝ)) (X := (82273036633475875373/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(606519879679139/7881300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12472009084321/197032500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (78813/100000 : ℝ)) (alpha := (606519879679139/7881300000000000 : ℝ)) (beta := (12472009084321/197032500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (78813/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(606519879679139/7881300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12472009084321/197032500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-226268789/5000000000 : ℝ)*X 0 0+(-748901717/1250000000 : ℝ)*X 0 1+(5369291429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3017282481/5000000000 : ℝ)*X 1 0+(3250713827/10000000000 : ℝ)*X 1 1+(3114265599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((71566631/125000000 : ℝ)*X 2 0+(-861403869/2500000000 : ℝ)*X 2 1+(-3279814851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-235695003/10000000000 : ℝ)*X 0 0+(-6823238783/10000000000 : ℝ)*X 0 1+(4587543977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5847139/9765625 : ℝ)*X 1 0+(4035013/12500000 : ℝ)*X 1 1+(1596453149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1177920487/2000000000 : ℝ)*X 2 0+(-1647836333/5000000000 : ℝ)*X 2 1+(-64798801/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3079012661/10000000000 : ℝ)*X 0 0+(-1481615759/10000000000 : ℝ)*X 0 1+(925371053/1250000000 : ℝ)*X 0 2+(3079012661/10000000000 : ℝ)*X 1 0+(-1481615759/10000000000 : ℝ)*X 1 1+(925371053/1250000000 : ℝ)*X 1 2+(3079012661/10000000000 : ℝ)*X 2 0+(-1481615759/10000000000 : ℝ)*X 2 1+(925371053/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-10429623/10000000000 : ℝ)*X 0 0+(-5789744903/10000000000 : ℝ)*X 0 1+(359866361/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6515996603/10000000000 : ℝ)*X 1 0+(766859667/2500000000 : ℝ)*X 1 1+(84771117/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6126233499/10000000000 : ℝ)*X 2 0+(-338009333/1000000000 : ℝ)*X 2 1+(-2870949829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3248609717/10000000000 : ℝ)*X 0 0+(-608092033/2500000000 : ℝ)*X 0 1+(6585726511/10000000000 : ℝ)*X 0 2+(3248609717/10000000000 : ℝ)*X 1 0+(-608092033/2500000000 : ℝ)*X 1 1+(6585726511/10000000000 : ℝ)*X 1 2+(3248609717/10000000000 : ℝ)*X 2 0+(-608092033/2500000000 : ℝ)*X 2 1+(6585726511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2253403/5000000000 : ℝ)*X 0 0+(-51139609/80000000 : ℝ)*X 0 1+(5138287567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3260959597/5000000000 : ℝ)*X 1 0+(370643119/1250000000 : ℝ)*X 1 1+(2809947593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((698492687/1250000000 : ℝ)*X 2 0+(-1779267089/5000000000 : ℝ)*X 2 1+(-415420711/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4618638859/10000000000 : ℝ)*X 0 0+(-1289020429/5000000000 : ℝ)*X 0 1+(5238926781/10000000000 : ℝ)*X 0 2+(4618638859/10000000000 : ℝ)*X 1 0+(-1289020429/5000000000 : ℝ)*X 1 1+(5238926781/10000000000 : ℝ)*X 1 2+(4618638859/10000000000 : ℝ)*X 2 0+(-1289020429/5000000000 : ℝ)*X 2 1+(5238926781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((4659/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4659/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3945459582419376395943207019/882625385880000000000000000000000 : ℝ) := by norm_num
    linear_combination (175988066103/250000000000 : ℝ)*(base40) + (1922121/500000000000 : ℝ)*(base60) + (171190291483/40000000000 : ℝ)*(major_s1_0) + (171190291483/40000000000 : ℝ)*(major_s1_1) + (171190291483/40000000000 : ℝ)*(major_s1_2) + (2871501/7812500000 : ℝ)*(sp_s1_1) + (43251383/500000000000 : ℝ)*(sp_s1_2) + (1228975117453/200000000000 : ℝ)*(sp_s1_7) + (3072354634381/500000000000 : ℝ)*(sp_s1_8) + (6144963988601/1000000000000 : ℝ)*(sp_s1_9) + (1207175012409/500000000000 : ℝ)*(sp_s1_13) + (13164761/500000000000 : ℝ)*(sp_s1_16) + (8623839/100000000000 : ℝ)*(sp_s1_20) + (1609869/8000000000 : ℝ)*(sp_s1_21) + (301804532901/125000000000 : ℝ)*(f.failure) + (6145076820889/1000000000000 : ℝ)*(f.sum) + (2586054455430813007/24785112240000000000000000000000 : ℝ)*base63 + (17581073338097/394065000000000000000000000 : ℝ)*base64 + (28115760377783/157240000000000000000000000 : ℝ)*base67 + (271523014369189/1576260000000000000000000000 : ℝ)*base69 + (37516458740020889/505191330000000000000000000000 : ℝ)*base70 + (9244469002501/44870000000000000000000000 : ℝ)*base73 + (44303162711187/62896000000000000000000000 : ℝ)*base75 + (13438459618747/26922000000000000000000000 : ℝ)*base76 + (118772551748525203/705535880000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (4943/12500000000000000 : ℝ)*base86 + (4943/12500000000000000 : ℝ)*base88 + (4943/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-2167/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2167/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37574320090277132245653854347/4728350281500000000000000000000000 : ℝ) := by norm_num
    linear_combination (475987/125000000000 : ℝ)*(base13) + (2292554544867/1000000000000 : ℝ)*(base40) + (171863651721/500000000000 : ℝ)*(base60) + (8201163582827/1000000000000 : ℝ)*(major_s1_0) + (8201163582827/1000000000000 : ℝ)*(major_s1_1) + (8201163582827/1000000000000 : ℝ)*(major_s1_2) + (8362871/250000000000 : ℝ)*(sp_s1_0) + (23582573/1000000000000 : ℝ)*(sp_s1_13) + (11775579379673/1000000000000 : ℝ)*(sp_s1_14) + (2943828177309/250000000000 : ℝ)*(sp_s1_15) + (11775616639053/1000000000000 : ℝ)*(sp_s1_16) + (925333858909/200000000000 : ℝ)*(sp_s1_20) + (303929817/1000000000000 : ℝ)*(sp_s1_22) + (15000611/1000000000000 : ℝ)*(sp_s1_27) + (462670787773/100000000000 : ℝ)*(f.failure) + (11775616639053/1000000000000 : ℝ)*(f.sum) + (79020988831873796569/619627806000000000000000000000000 : ℝ)*base62 + (4526281718263/98516250000000000000000000 : ℝ)*base64 + (1955945544821639/3931000000000000000000000000 : ℝ)*base67 + (1675054106180537/7881300000000000000000000000 : ℝ)*base68 + (1058212296528958019/6314891625000000000000000000000 : ℝ)*base70 + (68085271064827/560875000000000000000000000 : ℝ)*base73 + (543557644930167/7862000000000000000000000000 : ℝ)*base75 + (10224077050361/52582031250000000000000000 : ℝ)*base77 + (3584935034817176489/17638397000000000000000000000000 : ℝ)*base79 + (8661/10000000000000000 : ℝ)*base87 + (8661/10000000000000000 : ℝ)*base89 + (8661/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2239/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2239/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25342290923110262250281623901/4413126929400000000000000000000000 : ℝ) := by norm_num
    linear_combination (2394033/1000000000000 : ℝ)*(base39) + (77712318601/31250000000 : ℝ)*(base40) + (991/250000000000 : ℝ)*(base50) + (8329669210081/1000000000000 : ℝ)*(major_s1_0) + (8329669210081/1000000000000 : ℝ)*(major_s1_1) + (8329669210081/1000000000000 : ℝ)*(major_s1_2) + (15176491/1000000000000 : ℝ)*(sp_s1_0) + (29147039/500000000000 : ℝ)*(sp_s1_2) + (7561629/200000000000 : ℝ)*(sp_s1_7) + (178087661/1000000000000 : ℝ)*(sp_s1_15) + (1495009857253/125000000000 : ℝ)*(sp_s1_21) + (11959953754999/1000000000000 : ℝ)*(sp_s1_22) + (5980036774291/500000000000 : ℝ)*(sp_s1_23) + (4699204663331/1000000000000 : ℝ)*(sp_s1_27) + (4699204663331/1000000000000 : ℝ)*(f.failure) + (11960131842661/1000000000000 : ℝ)*(f.sum) + (152773025001024868693/619627806000000000000000000000000 : ℝ)*base63 + (609663609832987/788130000000000000000000000 : ℝ)*base64 + (2000039520749417/3931000000000000000000000000 : ℝ)*base67 + (6237639981472919/7881300000000000000000000000 : ℝ)*base69 + (2418507556168335539/12629783250000000000000000000000 : ℝ)*base70 + (903302576287387/1121750000000000000000000000 : ℝ)*base73 + (7443025104150301/7862000000000000000000000000 : ℝ)*base75 + (3160323822482063/3365250000000000000000000000 : ℝ)*base76 + (2065286557711495133/17638397000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (36933/100000000000000000 : ℝ)*base86 + (36933/100000000000000000 : ℝ)*base88 + (36933/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((13461/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13461/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3931/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3931/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78813/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(78813/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4659/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4659/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2167/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2167/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2239/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2239/6250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316086_s1 p hpa hpb X hX hprev0

#print axioms solution
