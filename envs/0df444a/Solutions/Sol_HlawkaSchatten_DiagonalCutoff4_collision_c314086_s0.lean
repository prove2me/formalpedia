-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314086_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:48:37.619986+00:00
-- url     : https://prove2.me/submissions/c27786b8-e3dc-431b-b8a6-bc3f7971504b

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
theorem collision_support_c314086_s0_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1283407071/2000000000 : ℝ)*x 0 + (3059786371/10000000000 : ℝ)*x 1 + (11405409/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1283407071/2000000000 : ℝ)^75 ≤ (56896577420601/100000000000000 : ℝ)^59 := by
    have hnat : (1283407071 : ℕ)^75*100000000000000^59 ≤ 56896577420601^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283407071 2000000000 56896577420601 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059786371/10000000000 : ℝ)^75 ≤ (22193076359771/100000000000000 : ℝ)^59 := by
    have hnat : (3059786371 : ℕ)^75*100000000000000^59 ≤ 22193076359771^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059786371 10000000000 22193076359771 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11405409/39062500 : ℝ)^75 ≤ (20910346208631/100000000000000 : ℝ)^59 := by
    have hnat : (11405409 : ℕ)^75*100000000000000^59 ≤ 20910346208631^59*39062500^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11405409 39062500 20910346208631 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1283407071/2000000000 : ℝ), (3059786371/10000000000 : ℝ), (11405409/39062500 : ℝ)] ![(56896577420601/100000000000000 : ℝ), (22193076359771/100000000000000 : ℝ), (20910346208631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1283407071/2000000000 : ℝ)|^75 ≤ (56896577420601/100000000000000 : ℝ)^59
        have hw : |(1283407071/2000000000 : ℝ)|=(1283407071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3059786371/10000000000 : ℝ)|^75 ≤ (22193076359771/100000000000000 : ℝ)^59
        have hw : |(3059786371/10000000000 : ℝ)|=(3059786371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11405409/39062500 : ℝ)|^75 ≤ (20910346208631/100000000000000 : ℝ)^59
        have hw : |(11405409/39062500 : ℝ)|=(11405409/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3010162691/5000000000 : ℝ)*x 0 + (-671408037/2000000000 : ℝ)*x 1 + (-775083389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3010162691/5000000000 : ℝ)^75 ≤ (26231667040081/50000000000000 : ℝ)^59 := by
    have hnat : (3010162691 : ℕ)^75*50000000000000^59 ≤ 26231667040081^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010162691 5000000000 26231667040081 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671408037/2000000000 : ℝ)^75 ≤ (6242267706953/25000000000000 : ℝ)^59 := by
    have hnat : (671408037 : ℕ)^75*25000000000000^59 ≤ 6242267706953^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671408037 2000000000 6242267706953 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775083389/2500000000 : ℝ)^75 ≤ (11283797536523/50000000000000 : ℝ)^59 := by
    have hnat : (775083389 : ℕ)^75*50000000000000^59 ≤ 11283797536523^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775083389 2500000000 11283797536523 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3010162691/5000000000 : ℝ), (-671408037/2000000000 : ℝ), (-775083389/2500000000 : ℝ)] ![(26231667040081/50000000000000 : ℝ), (6242267706953/25000000000000 : ℝ), (11283797536523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3010162691/5000000000 : ℝ)|^75 ≤ (26231667040081/50000000000000 : ℝ)^59
        have hw : |(3010162691/5000000000 : ℝ)|=(3010162691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-671408037/2000000000 : ℝ)|^75 ≤ (6242267706953/25000000000000 : ℝ)^59
        have hw : |(-671408037/2000000000 : ℝ)|=(671408037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-775083389/2500000000 : ℝ)|^75 ≤ (11283797536523/50000000000000 : ℝ)^59
        have hw : |(-775083389/2500000000 : ℝ)|=(775083389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (711645473/2000000000 : ℝ)*x 0 + (-2196594881/10000000000 : ℝ)*x 1 + (164083869/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (711645473/2000000000 : ℝ)^75 ≤ (840203294641/3125000000000 : ℝ)^59 := by
    have hnat : (711645473 : ℕ)^75*3125000000000^59 ≤ 840203294641^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711645473 2000000000 840203294641 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196594881/10000000000 : ℝ)^75 ≤ (7281342971881/50000000000000 : ℝ)^59 := by
    have hnat : (2196594881 : ℕ)^75*50000000000000^59 ≤ 7281342971881^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196594881 10000000000 7281342971881 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164083869/250000000 : ℝ)^75 ≤ (11710161724073/20000000000000 : ℝ)^59 := by
    have hnat : (164083869 : ℕ)^75*20000000000000^59 ≤ 11710161724073^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164083869 250000000 11710161724073 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(711645473/2000000000 : ℝ), (-2196594881/10000000000 : ℝ), (164083869/250000000 : ℝ)] ![(840203294641/3125000000000 : ℝ), (7281342971881/50000000000000 : ℝ), (11710161724073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(711645473/2000000000 : ℝ)|^75 ≤ (840203294641/3125000000000 : ℝ)^59
        have hw : |(711645473/2000000000 : ℝ)|=(711645473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2196594881/10000000000 : ℝ)|^75 ≤ (7281342971881/50000000000000 : ℝ)^59
        have hw : |(-2196594881/10000000000 : ℝ)|=(2196594881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164083869/250000000 : ℝ)|^75 ≤ (11710161724073/20000000000000 : ℝ)^59
        have hw : |(164083869/250000000 : ℝ)|=(164083869/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5785809/10000000000 : ℝ)*x 0 + (-1711400219/2000000000 : ℝ)*x 1 + (1295443909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5785809/10000000000 : ℝ)^75 ≤ (7662334987/100000000000000 : ℝ)^59 := by
    have hnat : (5785809 : ℕ)^75*100000000000000^59 ≤ 7662334987^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5785809 10000000000 7662334987 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1711400219/2000000000 : ℝ)^75 ≤ (41014566353463/50000000000000 : ℝ)^59 := by
    have hnat : (1711400219 : ℕ)^75*50000000000000^59 ≤ 41014566353463^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711400219 2000000000 41014566353463 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295443909/5000000000 : ℝ)^75 ≤ (17963204951931/100000000000000 : ℝ)^59 := by
    have hnat : (1295443909 : ℕ)^75*100000000000000^59 ≤ 17963204951931^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295443909 5000000000 17963204951931 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5785809/10000000000 : ℝ), (-1711400219/2000000000 : ℝ), (1295443909/5000000000 : ℝ)] ![(7662334987/100000000000000 : ℝ), (41014566353463/50000000000000 : ℝ), (17963204951931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5785809/10000000000 : ℝ)|^75 ≤ (7662334987/100000000000000 : ℝ)^59
        have hw : |(5785809/10000000000 : ℝ)|=(5785809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1711400219/2000000000 : ℝ)|^75 ≤ (41014566353463/50000000000000 : ℝ)^59
        have hw : |(-1711400219/2000000000 : ℝ)|=(1711400219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295443909/5000000000 : ℝ)|^75 ≤ (17963204951931/100000000000000 : ℝ)^59
        have hw : |(1295443909/5000000000 : ℝ)|=(1295443909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1919153969/5000000000 : ℝ)*x 0 + (40323253/62500000 : ℝ)*x 1 + (202197653/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1919153969/5000000000 : ℝ)^75 ≤ (1184197559977/4000000000000 : ℝ)^59 := by
    have hnat : (1919153969 : ℕ)^75*4000000000000^59 ≤ 1184197559977^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919153969 5000000000 1184197559977 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40323253/62500000 : ℝ)^75 ≤ (57287798267423/100000000000000 : ℝ)^59 := by
    have hnat : (40323253 : ℕ)^75*100000000000000^59 ≤ 57287798267423^59*62500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40323253 62500000 57287798267423 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202197653/1000000000 : ℝ)^75 ≤ (262145254449/2000000000000 : ℝ)^59 := by
    have hnat : (202197653 : ℕ)^75*2000000000000^59 ≤ 262145254449^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202197653 1000000000 262145254449 2000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1919153969/5000000000 : ℝ), (40323253/62500000 : ℝ), (202197653/1000000000 : ℝ)] ![(1184197559977/4000000000000 : ℝ), (57287798267423/100000000000000 : ℝ), (262145254449/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1919153969/5000000000 : ℝ)|^75 ≤ (1184197559977/4000000000000 : ℝ)^59
        have hw : |(1919153969/5000000000 : ℝ)|=(1919153969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40323253/62500000 : ℝ)|^75 ≤ (57287798267423/100000000000000 : ℝ)^59
        have hw : |(40323253/62500000 : ℝ)|=(40323253/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202197653/1000000000 : ℝ)|^75 ≤ (262145254449/2000000000000 : ℝ)^59
        have hw : |(202197653/1000000000 : ℝ)|=(202197653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8499576777/10000000000 : ℝ)*x 0 + (-26452579/250000000 : ℝ)*x 1 + (-49967279/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8499576777/10000000000 : ℝ)^75 ≤ (8133000643591/10000000000000 : ℝ)^59 := by
    have hnat : (8499576777 : ℕ)^75*10000000000000^59 ≤ 8133000643591^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8499576777 10000000000 8133000643591 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26452579/250000000 : ℝ)^75 ≤ (5754309735601/100000000000000 : ℝ)^59 := by
    have hnat : (26452579 : ℕ)^75*100000000000000^59 ≤ 5754309735601^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26452579 250000000 5754309735601 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49967279/250000000 : ℝ)^75 ≤ (645784190713/5000000000000 : ℝ)^59 := by
    have hnat : (49967279 : ℕ)^75*5000000000000^59 ≤ 645784190713^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49967279 250000000 645784190713 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8499576777/10000000000 : ℝ), (-26452579/250000000 : ℝ), (-49967279/250000000 : ℝ)] ![(8133000643591/10000000000000 : ℝ), (5754309735601/100000000000000 : ℝ), (645784190713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8499576777/10000000000 : ℝ)|^75 ≤ (8133000643591/10000000000000 : ℝ)^59
        have hw : |(8499576777/10000000000 : ℝ)|=(8499576777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26452579/250000000 : ℝ)|^75 ≤ (5754309735601/100000000000000 : ℝ)^59
        have hw : |(-26452579/250000000 : ℝ)|=(26452579/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49967279/250000000 : ℝ)|^75 ≤ (645784190713/5000000000000 : ℝ)^59
        have hw : |(-49967279/250000000 : ℝ)|=(49967279/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3644983119/10000000000 : ℝ)*x 0 + (-107786979/2500000000 : ℝ)*x 1 + (3795348413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3644983119/10000000000 : ℝ)^75 ≤ (27722557300559/100000000000000 : ℝ)^59 := by
    have hnat : (3644983119 : ℕ)^75*100000000000000^59 ≤ 27722557300559^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3644983119 10000000000 27722557300559 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107786979/2500000000 : ℝ)^75 ≤ (1838042101529/100000000000000 : ℝ)^59 := by
    have hnat : (107786979 : ℕ)^75*100000000000000^59 ≤ 1838042101529^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107786979 2500000000 1838042101529 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3795348413/5000000000 : ℝ)^75 ≤ (35219700294959/50000000000000 : ℝ)^59 := by
    have hnat : (3795348413 : ℕ)^75*50000000000000^59 ≤ 35219700294959^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3795348413 5000000000 35219700294959 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3644983119/10000000000 : ℝ), (-107786979/2500000000 : ℝ), (3795348413/5000000000 : ℝ)] ![(27722557300559/100000000000000 : ℝ), (1838042101529/100000000000000 : ℝ), (35219700294959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3644983119/10000000000 : ℝ)|^75 ≤ (27722557300559/100000000000000 : ℝ)^59
        have hw : |(3644983119/10000000000 : ℝ)|=(3644983119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107786979/2500000000 : ℝ)|^75 ≤ (1838042101529/100000000000000 : ℝ)^59
        have hw : |(-107786979/2500000000 : ℝ)|=(107786979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3795348413/5000000000 : ℝ)|^75 ≤ (35219700294959/50000000000000 : ℝ)^59
        have hw : |(3795348413/5000000000 : ℝ)|=(3795348413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-22101/2500000000 : ℝ)*x 0 + (-2003574241/5000000000 : ℝ)*x 1 + (7445392313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22101/2500000000 : ℝ)^75 ≤ (37672429/100000000000000 : ℝ)^59 := by
    have hnat : (22101 : ℕ)^75*100000000000000^59 ≤ 37672429^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22101 2500000000 37672429 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003574241/5000000000 : ℝ)^75 ≤ (15635068735463/50000000000000 : ℝ)^59 := by
    have hnat : (2003574241 : ℕ)^75*50000000000000^59 ≤ 15635068735463^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003574241 5000000000 15635068735463 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7445392313/10000000000 : ℝ)^75 ≤ (34364912424169/50000000000000 : ℝ)^59 := by
    have hnat : (7445392313 : ℕ)^75*50000000000000^59 ≤ 34364912424169^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7445392313 10000000000 34364912424169 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22101/2500000000 : ℝ), (-2003574241/5000000000 : ℝ), (7445392313/10000000000 : ℝ)] ![(37672429/100000000000000 : ℝ), (15635068735463/50000000000000 : ℝ), (34364912424169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22101/2500000000 : ℝ)|^75 ≤ (37672429/100000000000000 : ℝ)^59
        have hw : |(-22101/2500000000 : ℝ)|=(22101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2003574241/5000000000 : ℝ)|^75 ≤ (15635068735463/50000000000000 : ℝ)^59
        have hw : |(-2003574241/5000000000 : ℝ)|=(2003574241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7445392313/10000000000 : ℝ)|^75 ≤ (34364912424169/50000000000000 : ℝ)^59
        have hw : |(7445392313/10000000000 : ℝ)|=(7445392313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2146196331/2500000000 : ℝ)*x 0 + (29834463/125000000 : ℝ)*x 1 + (5585461/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146196331/2500000000 : ℝ)^75 ≤ (10295982008107/12500000000000 : ℝ)^59 := by
    have hnat : (2146196331 : ℕ)^75*12500000000000^59 ≤ 10295982008107^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146196331 2500000000 10295982008107 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29834463/125000000 : ℝ)^75 ≤ (16183715526151/100000000000000 : ℝ)^59 := by
    have hnat : (29834463 : ℕ)^75*100000000000000^59 ≤ 16183715526151^59*125000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29834463 125000000 16183715526151 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585461/156250000 : ℝ)^75 ≤ (181053549733/12500000000000 : ℝ)^59 := by
    have hnat : (5585461 : ℕ)^75*12500000000000^59 ≤ 181053549733^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585461 156250000 181053549733 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146196331/2500000000 : ℝ), (29834463/125000000 : ℝ), (5585461/156250000 : ℝ)] ![(10295982008107/12500000000000 : ℝ), (16183715526151/100000000000000 : ℝ), (181053549733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146196331/2500000000 : ℝ)|^75 ≤ (10295982008107/12500000000000 : ℝ)^59
        have hw : |(2146196331/2500000000 : ℝ)|=(2146196331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29834463/125000000 : ℝ)|^75 ≤ (16183715526151/100000000000000 : ℝ)^59
        have hw : |(29834463/125000000 : ℝ)|=(29834463/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585461/156250000 : ℝ)|^75 ≤ (181053549733/12500000000000 : ℝ)^59
        have hw : |(5585461/156250000 : ℝ)|=(5585461/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3957019581/5000000000 : ℝ)*x 0 + (-1012603147/5000000000 : ℝ)*x 1 + (-12243877/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3957019581/5000000000 : ℝ)^75 ≤ (74275428019017/100000000000000 : ℝ)^59 := by
    have hnat : (3957019581 : ℕ)^75*100000000000000^59 ≤ 74275428019017^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3957019581 5000000000 74275428019017 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012603147/5000000000 : ℝ)^75 ≤ (13133882838929/100000000000000 : ℝ)^59 := by
    have hnat : (1012603147 : ℕ)^75*100000000000000^59 ≤ 13133882838929^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012603147 5000000000 13133882838929 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12243877/62500000 : ℝ)^75 ≤ (2518137824987/20000000000000 : ℝ)^59 := by
    have hnat : (12243877 : ℕ)^75*20000000000000^59 ≤ 2518137824987^59*62500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12243877 62500000 2518137824987 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3957019581/5000000000 : ℝ), (-1012603147/5000000000 : ℝ), (-12243877/62500000 : ℝ)] ![(74275428019017/100000000000000 : ℝ), (13133882838929/100000000000000 : ℝ), (2518137824987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3957019581/5000000000 : ℝ)|^75 ≤ (74275428019017/100000000000000 : ℝ)^59
        have hw : |(3957019581/5000000000 : ℝ)|=(3957019581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1012603147/5000000000 : ℝ)|^75 ≤ (13133882838929/100000000000000 : ℝ)^59
        have hw : |(-1012603147/5000000000 : ℝ)|=(1012603147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12243877/62500000 : ℝ)|^75 ≤ (2518137824987/20000000000000 : ℝ)^59
        have hw : |(-12243877/62500000 : ℝ)|=(12243877/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (52413981/250000000 : ℝ)*x 0 + (-134087551/1000000000 : ℝ)*x 1 + (8265977179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52413981/250000000 : ℝ)^75 ≤ (1715612046527/12500000000000 : ℝ)^59 := by
    have hnat : (52413981 : ℕ)^75*12500000000000^59 ≤ 1715612046527^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52413981 250000000 1715612046527 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134087551/1000000000 : ℝ)^75 ≤ (7775852983289/100000000000000 : ℝ)^59 := by
    have hnat : (134087551 : ℕ)^75*100000000000000^59 ≤ 7775852983289^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134087551 1000000000 7775852983289 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8265977179/10000000000 : ℝ)^75 ≤ (78499250635391/100000000000000 : ℝ)^59 := by
    have hnat : (8265977179 : ℕ)^75*100000000000000^59 ≤ 78499250635391^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8265977179 10000000000 78499250635391 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52413981/250000000 : ℝ), (-134087551/1000000000 : ℝ), (8265977179/10000000000 : ℝ)] ![(1715612046527/12500000000000 : ℝ), (7775852983289/100000000000000 : ℝ), (78499250635391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52413981/250000000 : ℝ)|^75 ≤ (1715612046527/12500000000000 : ℝ)^59
        have hw : |(52413981/250000000 : ℝ)|=(52413981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134087551/1000000000 : ℝ)|^75 ≤ (7775852983289/100000000000000 : ℝ)^59
        have hw : |(-134087551/1000000000 : ℝ)|=(134087551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8265977179/10000000000 : ℝ)|^75 ≤ (78499250635391/100000000000000 : ℝ)^59
        have hw : |(8265977179/10000000000 : ℝ)|=(8265977179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (18307/312500000 : ℝ)*x 0 + (-553745003/625000000 : ℝ)*x 1 + (2160783921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18307/312500000 : ℝ)^75 ≤ (416910661/100000000000000 : ℝ)^59 := by
    have hnat : (18307 : ℕ)^75*100000000000000^59 ≤ 416910661^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18307 312500000 416910661 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553745003/625000000 : ℝ)^75 ≤ (10717253198501/12500000000000 : ℝ)^59 := by
    have hnat : (553745003 : ℕ)^75*12500000000000^59 ≤ 10717253198501^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553745003 625000000 10717253198501 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160783921/10000000000 : ℝ)^75 ≤ (14261557490417/100000000000000 : ℝ)^59 := by
    have hnat : (2160783921 : ℕ)^75*100000000000000^59 ≤ 14261557490417^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160783921 10000000000 14261557490417 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(18307/312500000 : ℝ), (-553745003/625000000 : ℝ), (2160783921/10000000000 : ℝ)] ![(416910661/100000000000000 : ℝ), (10717253198501/12500000000000 : ℝ), (14261557490417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(18307/312500000 : ℝ)|^75 ≤ (416910661/100000000000000 : ℝ)^59
        have hw : |(18307/312500000 : ℝ)|=(18307/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553745003/625000000 : ℝ)|^75 ≤ (10717253198501/12500000000000 : ℝ)^59
        have hw : |(-553745003/625000000 : ℝ)|=(553745003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2160783921/10000000000 : ℝ)|^75 ≤ (14261557490417/100000000000000 : ℝ)^59
        have hw : |(2160783921/10000000000 : ℝ)|=(2160783921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8824947837/10000000000 : ℝ)*x 0 + (242665853/2000000000 : ℝ)*x 1 + (135009941/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8824947837/10000000000 : ℝ)^75 ≤ (42654025252539/50000000000000 : ℝ)^59 := by
    have hnat : (8824947837 : ℕ)^75*50000000000000^59 ≤ 42654025252539^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8824947837 10000000000 42654025252539 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242665853/2000000000 : ℝ)^75 ≤ (1369607435409/20000000000000 : ℝ)^59 := by
    have hnat : (242665853 : ℕ)^75*20000000000000^59 ≤ 1369607435409^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242665853 2000000000 1369607435409 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135009941/1000000000 : ℝ)^75 ≤ (3921956154629/50000000000000 : ℝ)^59 := by
    have hnat : (135009941 : ℕ)^75*50000000000000^59 ≤ 3921956154629^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135009941 1000000000 3921956154629 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8824947837/10000000000 : ℝ), (242665853/2000000000 : ℝ), (135009941/1000000000 : ℝ)] ![(42654025252539/50000000000000 : ℝ), (1369607435409/20000000000000 : ℝ), (3921956154629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8824947837/10000000000 : ℝ)|^75 ≤ (42654025252539/50000000000000 : ℝ)^59
        have hw : |(8824947837/10000000000 : ℝ)|=(8824947837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242665853/2000000000 : ℝ)|^75 ≤ (1369607435409/20000000000000 : ℝ)^59
        have hw : |(242665853/2000000000 : ℝ)|=(242665853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135009941/1000000000 : ℝ)|^75 ≤ (3921956154629/50000000000000 : ℝ)^59
        have hw : |(135009941/1000000000 : ℝ)|=(135009941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3882456133/10000000000 : ℝ)*x 0 + (-3324496219/10000000000 : ℝ)*x 1 + (-2681834947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3882456133/10000000000 : ℝ)^75 ≤ (15019235657139/50000000000000 : ℝ)^59 := by
    have hnat : (3882456133 : ℕ)^75*50000000000000^59 ≤ 15019235657139^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3882456133 10000000000 15019235657139 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3324496219/10000000000 : ℝ)^75 ≤ (24661777610469/100000000000000 : ℝ)^59 := by
    have hnat : (3324496219 : ℕ)^75*100000000000000^59 ≤ 24661777610469^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3324496219 10000000000 24661777610469 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2681834947/5000000000 : ℝ)^75 ≤ (11324937764547/25000000000000 : ℝ)^59 := by
    have hnat : (2681834947 : ℕ)^75*25000000000000^59 ≤ 11324937764547^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681834947 5000000000 11324937764547 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3882456133/10000000000 : ℝ), (-3324496219/10000000000 : ℝ), (-2681834947/5000000000 : ℝ)] ![(15019235657139/50000000000000 : ℝ), (24661777610469/100000000000000 : ℝ), (11324937764547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3882456133/10000000000 : ℝ)|^75 ≤ (15019235657139/50000000000000 : ℝ)^59
        have hw : |(3882456133/10000000000 : ℝ)|=(3882456133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3324496219/10000000000 : ℝ)|^75 ≤ (24661777610469/100000000000000 : ℝ)^59
        have hw : |(-3324496219/10000000000 : ℝ)|=(3324496219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2681834947/5000000000 : ℝ)|^75 ≤ (11324937764547/25000000000000 : ℝ)^59
        have hw : |(-2681834947/5000000000 : ℝ)|=(2681834947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314086_s0_s0_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (463483741/625000000 : ℝ)*x 0 + (-332220641/5000000000 : ℝ)*x 1 + (3718250809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463483741/625000000 : ℝ)^75 ≤ (34191027162859/50000000000000 : ℝ)^59 := by
    have hnat : (463483741 : ℕ)^75*50000000000000^59 ≤ 34191027162859^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463483741 625000000 34191027162859 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332220641/5000000000 : ℝ)^75 ≤ (1592549024857/50000000000000 : ℝ)^59 := by
    have hnat : (332220641 : ℕ)^75*50000000000000^59 ≤ 1592549024857^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332220641 5000000000 1592549024857 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3718250809/10000000000 : ℝ)^75 ≤ (45492556171/160000000000 : ℝ)^59 := by
    have hnat : (3718250809 : ℕ)^75*160000000000^59 ≤ 45492556171^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718250809 10000000000 45492556171 160000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(463483741/625000000 : ℝ), (-332220641/5000000000 : ℝ), (3718250809/10000000000 : ℝ)] ![(34191027162859/50000000000000 : ℝ), (1592549024857/50000000000000 : ℝ), (45492556171/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(463483741/625000000 : ℝ)|^75 ≤ (34191027162859/50000000000000 : ℝ)^59
        have hw : |(463483741/625000000 : ℝ)|=(463483741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332220641/5000000000 : ℝ)|^75 ≤ (1592549024857/50000000000000 : ℝ)^59
        have hw : |(-332220641/5000000000 : ℝ)|=(332220641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3718250809/10000000000 : ℝ)|^75 ≤ (45492556171/160000000000 : ℝ)^59
        have hw : |(3718250809/10000000000 : ℝ)|=(3718250809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314086_s0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((71317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-81879/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-81879/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20471/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20471/25000 : ℝ)*X 1 2) := by
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
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((1283407071/2000000000 : ℝ)*X 1 0+(3059786371/10000000000 : ℝ)*X 1 1+(11405409/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3010162691/5000000000 : ℝ)*X 2 0+(-671408037/2000000000 : ℝ)*X 2 1+(-775083389/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((711645473/2000000000 : ℝ)*X 0 0+(-2196594881/10000000000 : ℝ)*X 0 1+(164083869/250000000 : ℝ)*X 0 2+(711645473/2000000000 : ℝ)*X 1 0+(-2196594881/10000000000 : ℝ)*X 1 1+(164083869/250000000 : ℝ)*X 1 2+(711645473/2000000000 : ℝ)*X 2 0+(-2196594881/10000000000 : ℝ)*X 2 1+(164083869/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((5785809/10000000000 : ℝ)*X 0 0+(-1711400219/2000000000 : ℝ)*X 0 1+(1295443909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1919153969/5000000000 : ℝ)*X 1 0+(40323253/62500000 : ℝ)*X 1 1+(202197653/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((8499576777/10000000000 : ℝ)*X 2 0+(-26452579/250000000 : ℝ)*X 2 1+(-49967279/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3644983119/10000000000 : ℝ)*X 0 0+(-107786979/2500000000 : ℝ)*X 0 1+(3795348413/5000000000 : ℝ)*X 0 2+(3644983119/10000000000 : ℝ)*X 1 0+(-107786979/2500000000 : ℝ)*X 1 1+(3795348413/5000000000 : ℝ)*X 1 2+(3644983119/10000000000 : ℝ)*X 2 0+(-107786979/2500000000 : ℝ)*X 2 1+(3795348413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-22101/2500000000 : ℝ)*X 0 0+(-2003574241/5000000000 : ℝ)*X 0 1+(7445392313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2146196331/2500000000 : ℝ)*X 1 0+(29834463/125000000 : ℝ)*X 1 1+(5585461/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3957019581/5000000000 : ℝ)*X 2 0+(-1012603147/5000000000 : ℝ)*X 2 1+(-12243877/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((52413981/250000000 : ℝ)*X 0 0+(-134087551/1000000000 : ℝ)*X 0 1+(8265977179/10000000000 : ℝ)*X 0 2+(52413981/250000000 : ℝ)*X 1 0+(-134087551/1000000000 : ℝ)*X 1 1+(8265977179/10000000000 : ℝ)*X 1 2+(52413981/250000000 : ℝ)*X 2 0+(-134087551/1000000000 : ℝ)*X 2 1+(8265977179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((18307/312500000 : ℝ)*X 0 0+(-553745003/625000000 : ℝ)*X 0 1+(2160783921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8824947837/10000000000 : ℝ)*X 1 0+(242665853/2000000000 : ℝ)*X 1 1+(135009941/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3882456133/10000000000 : ℝ)*X 2 0+(-3324496219/10000000000 : ℝ)*X 2 1+(-2681834947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((463483741/625000000 : ℝ)*X 0 0+(-332220641/5000000000 : ℝ)*X 0 1+(3718250809/10000000000 : ℝ)*X 0 2+(463483741/625000000 : ℝ)*X 1 0+(-332220641/5000000000 : ℝ)*X 1 1+(3718250809/10000000000 : ℝ)*X 1 2+(463483741/625000000 : ℝ)*X 2 0+(-332220641/5000000000 : ℝ)*X 2 1+(3718250809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314086_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((71317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (33112809188256571828269/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78647788851/125000000000 : ℝ)*(base7) + (12299711223/62500000000 : ℝ)*(base43) + (801534549769/1000000000000 : ℝ)*(base54) + (787741494553/500000000000 : ℝ)*(major_s0_0) + (1378687609539/1000000000000 : ℝ)*(major_s0_1) + (773948439337/1000000000000 : ℝ)*(major_s0_2) + (3940593/125000000000 : ℝ)*(sp_s0_6) + (1669976348591/1000000000000 : ℝ)*(sp_s0_7) + (933395091879/500000000000 : ℝ)*(sp_s0_8) + (868299367441/1000000000000 : ℝ)*(sp_s0_9) + (743222526211/1000000000000 : ℝ)*(sp_s0_13) + (8044349/50000000000 : ℝ)*(sp_s0_16) + (4882989/1000000000000 : ℝ)*(sp_s0_20) + (18455599/1000000000000 : ℝ)*(sp_s0_21) + (183122234581/200000000000 : ℝ)*(f.failure) + (933395091879/500000000000 : ℝ)*(f.sum) + (110573143893357/5000000000000000000000000000 : ℝ)*base62 + (3594399684845813/10000000000000000000000000000 : ℝ)*base64 + (40988863275043/400000000000000000000000000 : ℝ)*base66 + (199828084469769/400000000000000000000000000 : ℝ)*base68 + (589332530603863/10000000000000000000000000000 : ℝ)*base70 + (1291344370534203/5000000000000000000000000000 : ℝ)*base72 + (2639389931042489/10000000000000000000000000000 : ℝ)*base74 + (40909725975161/200000000000000000000000000 : ℝ)*base76 + (301728451055519/10000000000000000000000000000 : ℝ)*base79 + (1911/20000000000000000 : ℝ)*base86 + (21911/20000000000000000 : ℝ)*base88 + (1911/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-81879/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-81879/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15504811301035422702621/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1077557838479/1000000000000 : ℝ)*(base7) + (556217/100000000000 : ℝ)*(base31) + (144012315851/500000000000 : ℝ)*(base33) + (414939/1000000000000 : ℝ)*(base40) + (1256309756039/1000000000000 : ℝ)*(major_s0_0) + (1544334387741/1000000000000 : ℝ)*(major_s0_1) + (1544334387741/1000000000000 : ℝ)*(major_s0_2) + (9647/2500000000 : ℝ)*(sp_s0_1) + (6413639/500000000000 : ℝ)*(sp_s0_13) + (155994609459/100000000000 : ℝ)*(sp_s0_14) + (158987499589/125000000000 : ℝ)*(sp_s0_15) + (158990182861/125000000000 : ℝ)*(sp_s0_16) + (123440514499/62500000000 : ℝ)*(sp_s0_20) + (140859/8000000000 : ℝ)*(sp_s0_22) + (448754391477/500000000000 : ℝ)*(f.failure) + (155994609459/100000000000 : ℝ)*(f.sum) + (641427115413321/2500000000000000000000000000 : ℝ)*base63 + (5446869938791/10000000000000000000000000000 : ℝ)*base65 + (233919876463683/400000000000000000000000000 : ℝ)*base67 + (351236701623683/400000000000000000000000000 : ℝ)*base69 + (689174232225027/1250000000000000000000000000 : ℝ)*base71 + (4225765837486011/10000000000000000000000000000 : ℝ)*base73 + (1010357900061209/10000000000000000000000000000 : ℝ)*base75 + (152017503314457/400000000000000000000000000 : ℝ)*base77 + (1523230570539043/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (5913/50000000000000000 : ℝ)*base87 + (5913/50000000000000000 : ℝ)*base89 + (5913/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20471/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20471/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (52428122602479086057991/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298639/1000000000000 : ℝ)*(base1) + (877302077841/1000000000000 : ℝ)*(base7) + (3398824719/1000000000000 : ℝ)*(base33) + (927423160701/1000000000000 : ℝ)*(base43) + (1535774992473/1000000000000 : ℝ)*(major_s0_0) + (611750656491/1000000000000 : ℝ)*(major_s0_1) + (192396727149/125000000000 : ℝ)*(major_s0_2) + (26549061/1000000000000 : ℝ)*(sp_s0_2) + (932297/1000000000000 : ℝ)*(sp_s0_7) + (343983/250000000000 : ℝ)*(sp_s0_15) + (371252339639/500000000000 : ℝ)*(sp_s0_21) + (333305654597/200000000000 : ℝ)*(sp_s0_22) + (147815987831/200000000000 : ℝ)*(sp_s0_23) + (88590571679/50000000000 : ℝ)*(sp_s0_27) + (447254827189/500000000000 : ℝ)*(f.failure) + (417482118409/250000000000 : ℝ)*(f.sum) + (80700619232359/10000000000000000000000000000 : ℝ)*base63 + (717656947355599/1250000000000000000000000000 : ℝ)*base65 + (47579274405067/400000000000000000000000000 : ℝ)*base66 + (10694721789387/50000000000000000000000000 : ℝ)*base69 + (532550207689767/10000000000000000000000000000 : ℝ)*base71 + (20384415891877/10000000000000000000000000000 : ℝ)*base73 + (2999860796354959/10000000000000000000000000000 : ℝ)*base75 + (102084531313799/400000000000000000000000000 : ℝ)*base77 + (20461411882601/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (15959/50000000000000000 : ℝ)*base86 + (15959/50000000000000000 : ℝ)*base88 + (15959/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((71317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-81879/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-81879/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20471/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20471/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314086_s0 p hpa hpb X hX

#print axioms solution
