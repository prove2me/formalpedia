-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c323063_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:53:30.056985+00:00
-- url     : https://prove2.me/submissions/5f33d32b-1e78-4564-8660-10d028a88c1f

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
theorem collision_support_c323063_s0_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-40635239/2000000000 : ℝ)*x 0 + (5501061523/10000000000 : ℝ)*x 1 + (1458522981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40635239/2000000000 : ℝ)^21 ≤ (812316456663/100000000000000 : ℝ)^17 := by
    have hnat : (40635239 : ℕ)^21*100000000000000^17 ≤ 812316456663^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40635239 2000000000 812316456663 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501061523/10000000000 : ℝ)^21 ≤ (4779418835473/10000000000000 : ℝ)^17 := by
    have hnat : (5501061523 : ℕ)^21*10000000000000^17 ≤ 4779418835473^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501061523 10000000000 4779418835473 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458522981/2500000000 : ℝ)^21 ≤ (25696747588749/50000000000000 : ℝ)^17 := by
    have hnat : (1458522981 : ℕ)^21*50000000000000^17 ≤ 25696747588749^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458522981 2500000000 25696747588749 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40635239/2000000000 : ℝ), (5501061523/10000000000 : ℝ), (1458522981/2500000000 : ℝ)] ![(812316456663/100000000000000 : ℝ), (4779418835473/10000000000000 : ℝ), (25696747588749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40635239/2000000000 : ℝ)|^21 ≤ (812316456663/100000000000000 : ℝ)^17
        have hw : |(-40635239/2000000000 : ℝ)|=(40635239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501061523/10000000000 : ℝ)|^21 ≤ (4779418835473/10000000000000 : ℝ)^17
        have hw : |(5501061523/10000000000 : ℝ)|=(5501061523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458522981/2500000000 : ℝ)|^21 ≤ (25696747588749/50000000000000 : ℝ)^17
        have hw : |(1458522981/2500000000 : ℝ)|=(1458522981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5501060073/10000000000 : ℝ)*x 0 + (-25396909/1250000000 : ℝ)*x 1 + (5834093773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501060073/10000000000 : ℝ)^21 ≤ (1911766911707/4000000000000 : ℝ)^17 := by
    have hnat : (5501060073 : ℕ)^21*4000000000000^17 ≤ 1911766911707^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501060073 10000000000 1911766911707 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25396909/1250000000 : ℝ)^21 ≤ (812311898139/100000000000000 : ℝ)^17 := by
    have hnat : (25396909 : ℕ)^21*100000000000000^17 ≤ 812311898139^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25396909 1250000000 812311898139 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5834093773/10000000000 : ℝ)^21 ≤ (51393515298157/100000000000000 : ℝ)^17 := by
    have hnat : (5834093773 : ℕ)^21*100000000000000^17 ≤ 51393515298157^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5834093773 10000000000 51393515298157 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501060073/10000000000 : ℝ), (-25396909/1250000000 : ℝ), (5834093773/10000000000 : ℝ)] ![(1911766911707/4000000000000 : ℝ), (812311898139/100000000000000 : ℝ), (51393515298157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501060073/10000000000 : ℝ)|^21 ≤ (1911766911707/4000000000000 : ℝ)^17
        have hw : |(5501060073/10000000000 : ℝ)|=(5501060073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25396909/1250000000 : ℝ)|^21 ≤ (812311898139/100000000000000 : ℝ)^17
        have hw : |(-25396909/1250000000 : ℝ)|=(25396909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5834093773/10000000000 : ℝ)|^21 ≤ (51393515298157/100000000000000 : ℝ)^17
        have hw : |(5834093773/10000000000 : ℝ)|=(5834093773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2750530319/5000000000 : ℝ)*x 0 + (2917046583/5000000000 : ℝ)*x 1 + (-101587691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750530319/5000000000 : ℝ)^21 ≤ (4779417885651/10000000000000 : ℝ)^17 := by
    have hnat : (2750530319 : ℕ)^21*10000000000000^17 ≤ 4779417885651^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750530319 5000000000 4779417885651 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2917046583/5000000000 : ℝ)^21 ≤ (10278701738567/20000000000000 : ℝ)^17 := by
    have hnat : (2917046583 : ℕ)^21*20000000000000^17 ≤ 10278701738567^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2917046583 5000000000 10278701738567 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101587691/5000000000 : ℝ)^21 ≤ (12692381897/1562500000000 : ℝ)^17 := by
    have hnat : (101587691 : ℕ)^21*1562500000000^17 ≤ 12692381897^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101587691 5000000000 12692381897 1562500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750530319/5000000000 : ℝ), (2917046583/5000000000 : ℝ), (-101587691/5000000000 : ℝ)] ![(4779417885651/10000000000000 : ℝ), (10278701738567/20000000000000 : ℝ), (12692381897/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750530319/5000000000 : ℝ)|^21 ≤ (4779417885651/10000000000000 : ℝ)^17
        have hw : |(2750530319/5000000000 : ℝ)|=(2750530319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2917046583/5000000000 : ℝ)|^21 ≤ (10278701738567/20000000000000 : ℝ)^17
        have hw : |(2917046583/5000000000 : ℝ)|=(2917046583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101587691/5000000000 : ℝ)|^21 ≤ (12692381897/1562500000000 : ℝ)^17
        have hw : |(-101587691/5000000000 : ℝ)|=(101587691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-313370833/2500000000 : ℝ)*x 0 + (32822717/250000000 : ℝ)*x 1 + (8697682629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (313370833/2500000000 : ℝ)^21 ≤ (7689731333139/100000000000000 : ℝ)^17 := by
    have hnat : (313370833 : ℕ)^21*100000000000000^17 ≤ 7689731333139^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313370833 2500000000 7689731333139 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32822717/250000000 : ℝ)^21 ≤ (8142547278083/100000000000000 : ℝ)^17 := by
    have hnat : (32822717 : ℕ)^21*100000000000000^17 ≤ 8142547278083^17*250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32822717 250000000 8142547278083 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8697682629/10000000000 : ℝ)^21 ≤ (84167721369459/100000000000000 : ℝ)^17 := by
    have hnat : (8697682629 : ℕ)^21*100000000000000^17 ≤ 84167721369459^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8697682629 10000000000 84167721369459 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-313370833/2500000000 : ℝ), (32822717/250000000 : ℝ), (8697682629/10000000000 : ℝ)] ![(7689731333139/100000000000000 : ℝ), (8142547278083/100000000000000 : ℝ), (84167721369459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-313370833/2500000000 : ℝ)|^21 ≤ (7689731333139/100000000000000 : ℝ)^17
        have hw : |(-313370833/2500000000 : ℝ)|=(313370833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32822717/250000000 : ℝ)|^21 ≤ (8142547278083/100000000000000 : ℝ)^17
        have hw : |(32822717/250000000 : ℝ)|=(32822717/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8697682629/10000000000 : ℝ)|^21 ≤ (84167721369459/100000000000000 : ℝ)^17
        have hw : |(8697682629/10000000000 : ℝ)|=(8697682629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2230777193/10000000000 : ℝ)*x 0 + (-54338483/10000000000 : ℝ)*x 1 + (2174420669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2230777193/10000000000 : ℝ)^21 ≤ (3134597384119/20000000000000 : ℝ)^17 := by
    have hnat : (2230777193 : ℕ)^21*20000000000000^17 ≤ 3134597384119^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230777193 10000000000 3134597384119 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54338483/10000000000 : ℝ)^21 ≤ (159291143429/100000000000000 : ℝ)^17 := by
    have hnat : (54338483 : ℕ)^21*100000000000000^17 ≤ 159291143429^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54338483 10000000000 159291143429 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174420669/2500000000 : ℝ)^21 ≤ (2630241310353/3125000000000 : ℝ)^17 := by
    have hnat : (2174420669 : ℕ)^21*3125000000000^17 ≤ 2630241310353^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174420669 2500000000 2630241310353 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2230777193/10000000000 : ℝ), (-54338483/10000000000 : ℝ), (2174420669/2500000000 : ℝ)] ![(3134597384119/20000000000000 : ℝ), (159291143429/100000000000000 : ℝ), (2630241310353/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2230777193/10000000000 : ℝ)|^21 ≤ (3134597384119/20000000000000 : ℝ)^17
        have hw : |(2230777193/10000000000 : ℝ)|=(2230777193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54338483/10000000000 : ℝ)|^21 ≤ (159291143429/100000000000000 : ℝ)^17
        have hw : |(-54338483/10000000000 : ℝ)|=(54338483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2174420669/2500000000 : ℝ)|^21 ≤ (2630241310353/3125000000000 : ℝ)^17
        have hw : |(2174420669/2500000000 : ℝ)|=(2174420669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1115388217/5000000000 : ℝ)*x 0 + (8697683257/10000000000 : ℝ)*x 1 + (-54338383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115388217/5000000000 : ℝ)^21 ≤ (15672980333291/100000000000000 : ℝ)^17 := by
    have hnat : (1115388217 : ℕ)^21*100000000000000^17 ≤ 15672980333291^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115388217 5000000000 15672980333291 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8697683257/10000000000 : ℝ)^21 ≤ (21041932219139/25000000000000 : ℝ)^17 := by
    have hnat : (8697683257 : ℕ)^21*25000000000000^17 ≤ 21041932219139^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8697683257 10000000000 21041932219139 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54338383/10000000000 : ℝ)^21 ≤ (159290781307/100000000000000 : ℝ)^17 := by
    have hnat : (54338383 : ℕ)^21*100000000000000^17 ≤ 159290781307^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54338383 10000000000 159290781307 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115388217/5000000000 : ℝ), (8697683257/10000000000 : ℝ), (-54338383/10000000000 : ℝ)] ![(15672980333291/100000000000000 : ℝ), (21041932219139/25000000000000 : ℝ), (159290781307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115388217/5000000000 : ℝ)|^21 ≤ (15672980333291/100000000000000 : ℝ)^17
        have hw : |(1115388217/5000000000 : ℝ)|=(1115388217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8697683257/10000000000 : ℝ)|^21 ≤ (21041932219139/25000000000000 : ℝ)^17
        have hw : |(8697683257/10000000000 : ℝ)|=(8697683257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54338383/10000000000 : ℝ)|^21 ≤ (159290781307/100000000000000 : ℝ)^17
        have hw : |(-54338383/10000000000 : ℝ)|=(54338383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3139596057/10000000000 : ℝ)*x 0 + (7224404039/10000000000 : ℝ)*x 1 + (722826067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3139596057/10000000000 : ℝ)^21 ≤ (11952565660549/50000000000000 : ℝ)^17 := by
    have hnat : (3139596057 : ℕ)^21*50000000000000^17 ≤ 11952565660549^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3139596057 10000000000 11952565660549 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7224404039/10000000000 : ℝ)^21 ≤ (16730887650867/25000000000000 : ℝ)^17 := by
    have hnat : (7224404039 : ℕ)^21*25000000000000^17 ≤ 16730887650867^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7224404039 10000000000 16730887650867 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (722826067/5000000000 : ℝ)^21 ≤ (9171318059547/100000000000000 : ℝ)^17 := by
    have hnat : (722826067 : ℕ)^21*100000000000000^17 ≤ 9171318059547^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722826067 5000000000 9171318059547 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3139596057/10000000000 : ℝ), (7224404039/10000000000 : ℝ), (722826067/5000000000 : ℝ)] ![(11952565660549/50000000000000 : ℝ), (16730887650867/25000000000000 : ℝ), (9171318059547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3139596057/10000000000 : ℝ)|^21 ≤ (11952565660549/50000000000000 : ℝ)^17
        have hw : |(3139596057/10000000000 : ℝ)|=(3139596057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7224404039/10000000000 : ℝ)|^21 ≤ (16730887650867/25000000000000 : ℝ)^17
        have hw : |(7224404039/10000000000 : ℝ)|=(7224404039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(722826067/5000000000 : ℝ)|^21 ≤ (9171318059547/100000000000000 : ℝ)^17
        have hw : |(722826067/5000000000 : ℝ)|=(722826067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-19641003/10000000000 : ℝ)*x 0 + (1076498879/5000000000 : ℝ)*x 1 + (4381697569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19641003/10000000000 : ℝ)^21 ≤ (22658491783/50000000000000 : ℝ)^17 := by
    have hnat : (19641003 : ℕ)^21*50000000000000^17 ≤ 22658491783^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19641003 10000000000 22658491783 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076498879/5000000000 : ℝ)^21 ≤ (15000738995947/100000000000000 : ℝ)^17 := by
    have hnat : (1076498879 : ℕ)^21*100000000000000^17 ≤ 15000738995947^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076498879 5000000000 15000738995947 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381697569/5000000000 : ℝ)^21 ≤ (84953944007527/100000000000000 : ℝ)^17 := by
    have hnat : (4381697569 : ℕ)^21*100000000000000^17 ≤ 84953944007527^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381697569 5000000000 84953944007527 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19641003/10000000000 : ℝ), (1076498879/5000000000 : ℝ), (4381697569/5000000000 : ℝ)] ![(22658491783/50000000000000 : ℝ), (15000738995947/100000000000000 : ℝ), (84953944007527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19641003/10000000000 : ℝ)|^21 ≤ (22658491783/50000000000000 : ℝ)^17
        have hw : |(-19641003/10000000000 : ℝ)|=(19641003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076498879/5000000000 : ℝ)|^21 ≤ (15000738995947/100000000000000 : ℝ)^17
        have hw : |(1076498879/5000000000 : ℝ)|=(1076498879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4381697569/5000000000 : ℝ)|^21 ≤ (84953944007527/100000000000000 : ℝ)^17
        have hw : |(4381697569/5000000000 : ℝ)|=(4381697569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (73540879/625000000 : ℝ)*x 0 + (-1285657573/10000000000 : ℝ)*x 1 + (8763394999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73540879/625000000 : ℝ)^21 ≤ (888971711729/12500000000000 : ℝ)^17 := by
    have hnat : (73540879 : ℕ)^21*12500000000000^17 ≤ 888971711729^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73540879 625000000 888971711729 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285657573/10000000000 : ℝ)^21 ≤ (7934283948547/100000000000000 : ℝ)^17 := by
    have hnat : (1285657573 : ℕ)^21*100000000000000^17 ≤ 7934283948547^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285657573 10000000000 7934283948547 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8763394999/10000000000 : ℝ)^21 ≤ (84953942342979/100000000000000 : ℝ)^17 := by
    have hnat : (8763394999 : ℕ)^21*100000000000000^17 ≤ 84953942342979^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8763394999 10000000000 84953942342979 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(73540879/625000000 : ℝ), (-1285657573/10000000000 : ℝ), (8763394999/10000000000 : ℝ)] ![(888971711729/12500000000000 : ℝ), (7934283948547/100000000000000 : ℝ), (84953942342979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(73540879/625000000 : ℝ)|^21 ≤ (888971711729/12500000000000 : ℝ)^17
        have hw : |(73540879/625000000 : ℝ)|=(73540879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1285657573/10000000000 : ℝ)|^21 ≤ (7934283948547/100000000000000 : ℝ)^17
        have hw : |(-1285657573/10000000000 : ℝ)|=(1285657573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8763394999/10000000000 : ℝ)|^21 ≤ (84953942342979/100000000000000 : ℝ)^17
        have hw : |(8763394999/10000000000 : ℝ)|=(8763394999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4190856101/5000000000 : ℝ)*x 0 + (1316325763/5000000000 : ℝ)*x 1 + (-5274613/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190856101/5000000000 : ℝ)^21 ≤ (2010172832063/2500000000000 : ℝ)^17 := by
    have hnat : (4190856101 : ℕ)^21*2500000000000^17 ≤ 2010172832063^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190856101 5000000000 2010172832063 2500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316325763/5000000000 : ℝ)^21 ≤ (19231596926507/100000000000000 : ℝ)^17 := by
    have hnat : (1316325763 : ℕ)^21*100000000000000^17 ≤ 19231596926507^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316325763 5000000000 19231596926507 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274613/500000000 : ℝ)^21 ≤ (180744893109/50000000000000 : ℝ)^17 := by
    have hnat : (5274613 : ℕ)^21*50000000000000^17 ≤ 180744893109^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274613 500000000 180744893109 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190856101/5000000000 : ℝ), (1316325763/5000000000 : ℝ), (-5274613/500000000 : ℝ)] ![(2010172832063/2500000000000 : ℝ), (19231596926507/100000000000000 : ℝ), (180744893109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190856101/5000000000 : ℝ)|^21 ≤ (2010172832063/2500000000000 : ℝ)^17
        have hw : |(4190856101/5000000000 : ℝ)|=(4190856101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316325763/5000000000 : ℝ)|^21 ≤ (19231596926507/100000000000000 : ℝ)^17
        have hw : |(1316325763/5000000000 : ℝ)|=(1316325763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5274613/500000000 : ℝ)|^21 ≤ (180744893109/50000000000000 : ℝ)^17
        have hw : |(-5274613/500000000 : ℝ)|=(5274613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7567969581/10000000000 : ℝ)*x 0 + (675989299/2500000000 : ℝ)*x 1 + (291038481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7567969581/10000000000 : ℝ)^21 ≤ (70876773201189/100000000000000 : ℝ)^17 := by
    have hnat : (7567969581 : ℕ)^21*100000000000000^17 ≤ 70876773201189^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7567969581 10000000000 70876773201189 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675989299/2500000000 : ℝ)^21 ≤ (19877085664943/100000000000000 : ℝ)^17 := by
    have hnat : (675989299 : ℕ)^21*100000000000000^17 ≤ 19877085664943^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675989299 2500000000 19877085664943 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291038481/2000000000 : ℝ)^21 ≤ (46230705647/500000000000 : ℝ)^17 := by
    have hnat : (291038481 : ℕ)^21*500000000000^17 ≤ 46230705647^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291038481 2000000000 46230705647 500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7567969581/10000000000 : ℝ), (675989299/2500000000 : ℝ), (291038481/2000000000 : ℝ)] ![(70876773201189/100000000000000 : ℝ), (19877085664943/100000000000000 : ℝ), (46230705647/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7567969581/10000000000 : ℝ)|^21 ≤ (70876773201189/100000000000000 : ℝ)^17
        have hw : |(7567969581/10000000000 : ℝ)|=(7567969581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675989299/2500000000 : ℝ)|^21 ≤ (19877085664943/100000000000000 : ℝ)^17
        have hw : |(675989299/2500000000 : ℝ)|=(675989299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(291038481/2000000000 : ℝ)|^21 ≤ (46230705647/500000000000 : ℝ)^17
        have hw : |(291038481/2000000000 : ℝ)|=(291038481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-75305811/5000000000 : ℝ)*x 0 + (1508404563/2000000000 : ℝ)*x 1 + (3656978241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75305811/5000000000 : ℝ)^21 ≤ (3507513273/625000000000 : ℝ)^17 := by
    have hnat : (75305811 : ℕ)^21*625000000000^17 ≤ 3507513273^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75305811 5000000000 3507513273 625000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1508404563/2000000000 : ℝ)^21 ≤ (70576716862651/100000000000000 : ℝ)^17 := by
    have hnat : (1508404563 : ℕ)^21*100000000000000^17 ≤ 70576716862651^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508404563 2000000000 70576716862651 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3656978241/10000000000 : ℝ)^21 ≤ (7215520252107/25000000000000 : ℝ)^17 := by
    have hnat : (3656978241 : ℕ)^21*25000000000000^17 ≤ 7215520252107^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3656978241 10000000000 7215520252107 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75305811/5000000000 : ℝ), (1508404563/2000000000 : ℝ), (3656978241/10000000000 : ℝ)] ![(3507513273/625000000000 : ℝ), (70576716862651/100000000000000 : ℝ), (7215520252107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75305811/5000000000 : ℝ)|^21 ≤ (3507513273/625000000000 : ℝ)^17
        have hw : |(-75305811/5000000000 : ℝ)|=(75305811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1508404563/2000000000 : ℝ)|^21 ≤ (70576716862651/100000000000000 : ℝ)^17
        have hw : |(1508404563/2000000000 : ℝ)|=(1508404563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3656978241/10000000000 : ℝ)|^21 ≤ (7215520252107/25000000000000 : ℝ)^17
        have hw : |(3656978241/10000000000 : ℝ)|=(3656978241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8319395837/10000000000 : ℝ)*x 0 + (-247619/125000000 : ℝ)*x 1 + (2748803037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8319395837/10000000000 : ℝ)^21 ≤ (39834544985509/50000000000000 : ℝ)^17 := by
    have hnat : (8319395837 : ℕ)^21*50000000000000^17 ≤ 39834544985509^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8319395837 10000000000 39834544985509 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247619/125000000 : ℝ)^21 ≤ (9159553207/20000000000000 : ℝ)^17 := by
    have hnat : (247619 : ℕ)^21*20000000000000^17 ≤ 9159553207^17*125000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247619 125000000 9159553207 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748803037/10000000000 : ℝ)^21 ≤ (20285112255641/100000000000000 : ℝ)^17 := by
    have hnat : (2748803037 : ℕ)^21*100000000000000^17 ≤ 20285112255641^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748803037 10000000000 20285112255641 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8319395837/10000000000 : ℝ), (-247619/125000000 : ℝ), (2748803037/10000000000 : ℝ)] ![(39834544985509/50000000000000 : ℝ), (9159553207/20000000000000 : ℝ), (20285112255641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8319395837/10000000000 : ℝ)|^21 ≤ (39834544985509/50000000000000 : ℝ)^17
        have hw : |(8319395837/10000000000 : ℝ)|=(8319395837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-247619/125000000 : ℝ)|^21 ≤ (9159553207/20000000000000 : ℝ)^17
        have hw : |(-247619/125000000 : ℝ)|=(247619/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748803037/10000000000 : ℝ)|^21 ≤ (20285112255641/100000000000000 : ℝ)^17
        have hw : |(2748803037/10000000000 : ℝ)|=(2748803037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (180547059/2000000000 : ℝ)*x 0 + (8944706159/10000000000 : ℝ)*x 1 + (-315133557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180547059/2000000000 : ℝ)^21 ≤ (2563184914209/50000000000000 : ℝ)^17 := by
    have hnat : (180547059 : ℕ)^21*50000000000000^17 ≤ 2563184914209^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180547059 2000000000 2563184914209 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8944706159/10000000000 : ℝ)^21 ≤ (87130430796971/100000000000000 : ℝ)^17 := by
    have hnat : (8944706159 : ℕ)^21*100000000000000^17 ≤ 87130430796971^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8944706159 10000000000 87130430796971 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315133557/2500000000 : ℝ)^21 ≤ (3871599681533/50000000000000 : ℝ)^17 := by
    have hnat : (315133557 : ℕ)^21*50000000000000^17 ≤ 3871599681533^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315133557 2500000000 3871599681533 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180547059/2000000000 : ℝ), (8944706159/10000000000 : ℝ), (-315133557/2500000000 : ℝ)] ![(2563184914209/50000000000000 : ℝ), (87130430796971/100000000000000 : ℝ), (3871599681533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180547059/2000000000 : ℝ)|^21 ≤ (2563184914209/50000000000000 : ℝ)^17
        have hw : |(180547059/2000000000 : ℝ)|=(180547059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8944706159/10000000000 : ℝ)|^21 ≤ (87130430796971/100000000000000 : ℝ)^17
        have hw : |(8944706159/10000000000 : ℝ)|=(8944706159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315133557/2500000000 : ℝ)|^21 ≤ (3871599681533/50000000000000 : ℝ)^17
        have hw : |(-315133557/2500000000 : ℝ)|=(315133557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s0_s0_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7683696927/10000000000 : ℝ)*x 0 + (1204765797/5000000000 : ℝ)*x 1 + (202294919/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7683696927/10000000000 : ℝ)^21 ≤ (72218019424863/100000000000000 : ℝ)^17 := by
    have hnat : (7683696927 : ℕ)^21*100000000000000^17 ≤ 72218019424863^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7683696927 10000000000 72218019424863 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204765797/5000000000 : ℝ)^21 ≤ (3447743935619/20000000000000 : ℝ)^17 := by
    have hnat : (1204765797 : ℕ)^21*20000000000000^17 ≤ 3447743935619^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204765797 5000000000 3447743935619 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202294919/1250000000 : ℝ)^21 ≤ (5271630441173/50000000000000 : ℝ)^17 := by
    have hnat : (202294919 : ℕ)^21*50000000000000^17 ≤ 5271630441173^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202294919 1250000000 5271630441173 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7683696927/10000000000 : ℝ), (1204765797/5000000000 : ℝ), (202294919/1250000000 : ℝ)] ![(72218019424863/100000000000000 : ℝ), (3447743935619/20000000000000 : ℝ), (5271630441173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7683696927/10000000000 : ℝ)|^21 ≤ (72218019424863/100000000000000 : ℝ)^17
        have hw : |(7683696927/10000000000 : ℝ)|=(7683696927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204765797/5000000000 : ℝ)|^21 ≤ (3447743935619/20000000000000 : ℝ)^17
        have hw : |(1204765797/5000000000 : ℝ)|=(1204765797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202294919/1250000000 : ℝ)|^21 ≤ (5271630441173/50000000000000 : ℝ)^17
        have hw : |(202294919/1250000000 : ℝ)|=(202294919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323063_s0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((4333/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4333/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8641/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8641/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16703/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16703/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-40635239/2000000000 : ℝ)*X 0 0+(5501061523/10000000000 : ℝ)*X 0 1+(1458522981/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5501060073/10000000000 : ℝ)*X 1 0+(-25396909/1250000000 : ℝ)*X 1 1+(5834093773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2750530319/5000000000 : ℝ)*X 2 0+(2917046583/5000000000 : ℝ)*X 2 1+(-101587691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-313370833/2500000000 : ℝ)*X 0 0+(32822717/250000000 : ℝ)*X 0 1+(8697682629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2230777193/10000000000 : ℝ)*X 1 0+(-54338483/10000000000 : ℝ)*X 1 1+(2174420669/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1115388217/5000000000 : ℝ)*X 2 0+(8697683257/10000000000 : ℝ)*X 2 1+(-54338383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3139596057/10000000000 : ℝ)*X 0 0+(7224404039/10000000000 : ℝ)*X 0 1+(722826067/5000000000 : ℝ)*X 0 2+(3139596057/10000000000 : ℝ)*X 1 0+(7224404039/10000000000 : ℝ)*X 1 1+(722826067/5000000000 : ℝ)*X 1 2+(3139596057/10000000000 : ℝ)*X 2 0+(7224404039/10000000000 : ℝ)*X 2 1+(722826067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-19641003/10000000000 : ℝ)*X 0 0+(1076498879/5000000000 : ℝ)*X 0 1+(4381697569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((73540879/625000000 : ℝ)*X 1 0+(-1285657573/10000000000 : ℝ)*X 1 1+(8763394999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4190856101/5000000000 : ℝ)*X 2 0+(1316325763/5000000000 : ℝ)*X 2 1+(-5274613/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7567969581/10000000000 : ℝ)*X 0 0+(675989299/2500000000 : ℝ)*X 0 1+(291038481/2000000000 : ℝ)*X 0 2+(7567969581/10000000000 : ℝ)*X 1 0+(675989299/2500000000 : ℝ)*X 1 1+(291038481/2000000000 : ℝ)*X 1 2+(7567969581/10000000000 : ℝ)*X 2 0+(675989299/2500000000 : ℝ)*X 2 1+(291038481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-75305811/5000000000 : ℝ)*X 0 0+(1508404563/2000000000 : ℝ)*X 0 1+(3656978241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8319395837/10000000000 : ℝ)*X 1 0+(-247619/125000000 : ℝ)*X 1 1+(2748803037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((180547059/2000000000 : ℝ)*X 2 0+(8944706159/10000000000 : ℝ)*X 2 1+(-315133557/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7683696927/10000000000 : ℝ)*X 0 0+(1204765797/5000000000 : ℝ)*X 0 1+(202294919/1250000000 : ℝ)*X 0 2+(7683696927/10000000000 : ℝ)*X 1 0+(1204765797/5000000000 : ℝ)*X 1 1+(202294919/1250000000 : ℝ)*X 1 2+(7683696927/10000000000 : ℝ)*X 2 0+(1204765797/5000000000 : ℝ)*X 2 1+(202294919/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4333/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4333/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2599726059523987043211/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1136950679121/1000000000000 : ℝ)*(base7) + (922051/1000000000000 : ℝ)*(base50) + (1127957/1000000000000 : ℝ)*(base60) + (698972876953/500000000000 : ℝ)*(major_s0_0) + (698972876953/500000000000 : ℝ)*(major_s0_1) + (698972876953/500000000000 : ℝ)*(major_s0_2) + (1032167/250000000000 : ℝ)*(sp_s0_0) + (321823/1000000000000 : ℝ)*(sp_s0_1) + (181104295847/125000000000 : ℝ)*(sp_s0_7) + (1448864787017/1000000000000 : ℝ)*(sp_s0_8) + (724432598569/500000000000 : ℝ)*(sp_s0_9) + (185152266247/100000000000 : ℝ)*(sp_s0_13) + (13350847/500000000000 : ℝ)*(sp_s0_14) + (88297/1000000000000 : ℝ)*(sp_s0_15) + (714571983349/1000000000000 : ℝ)*(f.failure) + (724432598569/500000000000 : ℝ)*(f.sum) + (141437326897581/500000000000000000000000000 : ℝ)*base62 + (2629765329706009/5000000000000000000000000000 : ℝ)*base65 + (554659998706009/5000000000000000000000000000 : ℝ)*base67 + (30422348102419/1000000000000000000000000000 : ℝ)*base69 + (302157415152263/625000000000000000000000000 : ℝ)*base71 + (4855871365706009/5000000000000000000000000000 : ℝ)*base73 + (309544295702419/1000000000000000000000000000 : ℝ)*base75 + (277533484302419/1000000000000000000000000000 : ℝ)*base77 + (381462738793991/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (50867/50000000000000000 : ℝ)*base86 + (50867/50000000000000000 : ℝ)*base88 + (50867/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8641/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8641/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (79537172455896058733619/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1141515253187/1000000000000 : ℝ)*(base7) + (1297133/1000000000000 : ℝ)*(base27) + (243/31250000000 : ℝ)*(base39) + (370019/1000000000000 : ℝ)*(base49) + (11508653181/1000000000000 : ℝ)*(base53) + (1358990592239/1000000000000 : ℝ)*(major_s0_0) + (1358990592239/1000000000000 : ℝ)*(major_s0_1) + (1347481939057/1000000000000 : ℝ)*(major_s0_2) + (1631667/31250000000 : ℝ)*(sp_s0_8) + (1376816821163/1000000000000 : ℝ)*(sp_s0_14) + (688382303909/500000000000 : ℝ)*(sp_s0_15) + (173540684293/125000000000 : ℝ)*(sp_s0_16) + (1836056282971/1000000000000 : ℝ)*(sp_s0_20) + (58695421/500000000000 : ℝ)*(sp_s0_27) + (347329858879/500000000000 : ℝ)*(f.failure) + (173540684293/125000000000 : ℝ)*(f.sum) + (38457875985631/62500000000000000000000000 : ℝ)*base62 + (2214013928217521/10000000000000000000000000000 : ℝ)*base65 + (12337308383778833/10000000000000000000000000000 : ℝ)*base66 + (239293639409189/2000000000000000000000000000 : ℝ)*base68 + (459542422718747/5000000000000000000000000000 : ℝ)*base70 + (4090066384221167/10000000000000000000000000000 : ℝ)*base73 + (836693473331003/2000000000000000000000000000 : ℝ)*base74 + (650101079668997/2000000000000000000000000000 : ℝ)*base77 + (632630649721167/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (7857/25000000000000000 : ℝ)*base86 + (7857/25000000000000000 : ℝ)*base88 + (17143/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16703/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16703/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19551236338102010126247/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (285647976991/250000000000 : ℝ)*(base7) + (854369/500000000000 : ℝ)*(base27) + (61224583977/500000000000 : ℝ)*(base40) + (509177/100000000000 : ℝ)*(base43) + (678001/1000000000000 : ℝ)*(base49) + (666260997353/500000000000 : ℝ)*(major_s0_0) + (266503380587/200000000000 : ℝ)*(major_s0_1) + (666260997353/500000000000 : ℝ)*(major_s0_2) + (2712359/1000000000000 : ℝ)*(sp_s0_2) + (22068867/1000000000000 : ℝ)*(sp_s0_9) + (1348316623449/1000000000000 : ℝ)*(sp_s0_21) + (67416085761/50000000000 : ℝ)*(sp_s0_22) + (1348291842223/1000000000000 : ℝ)*(sp_s0_23) + (113982516621/62500000000 : ℝ)*(sp_s0_27) + (681130066709/1000000000000 : ℝ)*(f.failure) + (67416085761/50000000000 : ℝ)*(f.sum) + (652885851101757/2000000000000000000000000000 : ℝ)*base62 + (799921899412791/5000000000000000000000000000 : ℝ)*base64 + (221623491306389/2000000000000000000000000000 : ℝ)*base66 + (258600509528381/1000000000000000000000000000 : ℝ)*base68 + (253409515805663/625000000000000000000000000 : ℝ)*base71 + (1920814745912791/5000000000000000000000000000 : ℝ)*base72 + (38485294208999/400000000000000000000000000 : ℝ)*base74 + (293668086271619/1000000000000000000000000000 : ℝ)*base77 + (7738140084357527/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (25747/50000000000000000 : ℝ)*base86 + (24253/50000000000000000 : ℝ)*base89 + (25747/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((4333/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4333/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8641/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8641/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16703/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16703/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c323063_s0 p hpa hpb X hX

#print axioms solution
