-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c319083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:31:35.511657+00:00
-- url     : https://prove2.me/submissions/6321fe8e-4e18-4cc3-b62b-c5228cbf89a7

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
theorem collision_support_c319083_s1_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1142614289/5000000000 : ℝ)*x 0 + (596239083/1250000000 : ℝ)*x 1 + (40920567/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1142614289/5000000000 : ℝ)^5 ≤ (158001808567/1000000000000 : ℝ)^4 := by
    have hnat : (1142614289 : ℕ)^5*1000000000000^4 ≤ 158001808567^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142614289 5000000000 158001808567 1000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596239083/1250000000 : ℝ)^5 ≤ (39640400540721/100000000000000 : ℝ)^4 := by
    have hnat : (596239083 : ℕ)^5*100000000000000^4 ≤ 39640400540721^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596239083 1250000000 39640400540721 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40920567/78125000 : ℝ)^5 ≤ (11139854645269/25000000000000 : ℝ)^4 := by
    have hnat : (40920567 : ℕ)^5*25000000000000^4 ≤ 11139854645269^4*78125000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40920567 78125000 11139854645269 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1142614289/5000000000 : ℝ), (596239083/1250000000 : ℝ), (40920567/78125000 : ℝ)] ![(158001808567/1000000000000 : ℝ), (39640400540721/100000000000000 : ℝ), (11139854645269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1142614289/5000000000 : ℝ)|^5 ≤ (158001808567/1000000000000 : ℝ)^4
        have hw : |(-1142614289/5000000000 : ℝ)|=(1142614289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596239083/1250000000 : ℝ)|^5 ≤ (39640400540721/100000000000000 : ℝ)^4
        have hw : |(596239083/1250000000 : ℝ)|=(596239083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40920567/78125000 : ℝ)|^5 ≤ (11139854645269/25000000000000 : ℝ)^4
        have hw : |(40920567/78125000 : ℝ)|=(40920567/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1678354303/2500000000 : ℝ)*x 0 + (-855217093/10000000000 : ℝ)*x 1 + (2139421907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1678354303/2500000000 : ℝ)^5 ≤ (60768644218383/100000000000000 : ℝ)^4 := by
    have hnat : (1678354303 : ℕ)^5*100000000000000^4 ≤ 60768644218383^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678354303 2500000000 60768644218383 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855217093/10000000000 : ℝ)^5 ≤ (578103340007/12500000000000 : ℝ)^4 := by
    have hnat : (855217093 : ℕ)^5*12500000000000^4 ≤ 578103340007^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855217093 10000000000 578103340007 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139421907/5000000000 : ℝ)^5 ≤ (34606529044703/100000000000000 : ℝ)^4 := by
    have hnat : (2139421907 : ℕ)^5*100000000000000^4 ≤ 34606529044703^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139421907 5000000000 34606529044703 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1678354303/2500000000 : ℝ), (-855217093/10000000000 : ℝ), (2139421907/5000000000 : ℝ)] ![(60768644218383/100000000000000 : ℝ), (578103340007/12500000000000 : ℝ), (34606529044703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1678354303/2500000000 : ℝ)|^5 ≤ (60768644218383/100000000000000 : ℝ)^4
        have hw : |(1678354303/2500000000 : ℝ)|=(1678354303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855217093/10000000000 : ℝ)|^5 ≤ (578103340007/12500000000000 : ℝ)^4
        have hw : |(-855217093/10000000000 : ℝ)|=(855217093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2139421907/5000000000 : ℝ)|^5 ≤ (34606529044703/100000000000000 : ℝ)^4
        have hw : |(2139421907/5000000000 : ℝ)|=(2139421907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3547381337/10000000000 : ℝ)*x 0 + (6337028871/10000000000 : ℝ)*x 1 + (-2317882197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3547381337/10000000000 : ℝ)^5 ≤ (547538726747/2000000000000 : ℝ)^4 := by
    have hnat : (3547381337 : ℕ)^5*2000000000000^4 ≤ 547538726747^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3547381337 10000000000 547538726747 2000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6337028871/10000000000 : ℝ)^5 ≤ (28270084819187/50000000000000 : ℝ)^4 := by
    have hnat : (6337028871 : ℕ)^5*50000000000000^4 ≤ 28270084819187^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6337028871 10000000000 28270084819187 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2317882197/10000000000 : ℝ)^5 ≤ (16082894006251/100000000000000 : ℝ)^4 := by
    have hnat : (2317882197 : ℕ)^5*100000000000000^4 ≤ 16082894006251^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317882197 10000000000 16082894006251 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3547381337/10000000000 : ℝ), (6337028871/10000000000 : ℝ), (-2317882197/10000000000 : ℝ)] ![(547538726747/2000000000000 : ℝ), (28270084819187/50000000000000 : ℝ), (16082894006251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3547381337/10000000000 : ℝ)|^5 ≤ (547538726747/2000000000000 : ℝ)^4
        have hw : |(3547381337/10000000000 : ℝ)|=(3547381337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6337028871/10000000000 : ℝ)|^5 ≤ (28270084819187/50000000000000 : ℝ)^4
        have hw : |(6337028871/10000000000 : ℝ)|=(6337028871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2317882197/10000000000 : ℝ)|^5 ≤ (16082894006251/100000000000000 : ℝ)^4
        have hw : |(-2317882197/10000000000 : ℝ)|=(2317882197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-2340783757/10000000000 : ℝ)*x 0 + (4729644427/10000000000 : ℝ)*x 1 + (2615919831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2340783757/10000000000 : ℝ)^5 ≤ (508805316543/3125000000000 : ℝ)^4 := by
    have hnat : (2340783757 : ℕ)^5*3125000000000^4 ≤ 508805316543^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340783757 10000000000 508805316543 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4729644427/10000000000 : ℝ)^5 ≤ (4902816373829/12500000000000 : ℝ)^4 := by
    have hnat : (4729644427 : ℕ)^5*12500000000000^4 ≤ 4902816373829^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4729644427 10000000000 4902816373829 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615919831/5000000000 : ℝ)^5 ≤ (11123924716447/25000000000000 : ℝ)^4 := by
    have hnat : (2615919831 : ℕ)^5*25000000000000^4 ≤ 11123924716447^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615919831 5000000000 11123924716447 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2340783757/10000000000 : ℝ), (4729644427/10000000000 : ℝ), (2615919831/5000000000 : ℝ)] ![(508805316543/3125000000000 : ℝ), (4902816373829/12500000000000 : ℝ), (11123924716447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2340783757/10000000000 : ℝ)|^5 ≤ (508805316543/3125000000000 : ℝ)^4
        have hw : |(-2340783757/10000000000 : ℝ)|=(2340783757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4729644427/10000000000 : ℝ)|^5 ≤ (4902816373829/12500000000000 : ℝ)^4
        have hw : |(4729644427/10000000000 : ℝ)|=(4729644427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615919831/5000000000 : ℝ)|^5 ≤ (11123924716447/25000000000000 : ℝ)^4
        have hw : |(2615919831/5000000000 : ℝ)|=(2615919831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (812894587/1250000000 : ℝ)*x 0 + (-66029179/5000000000 : ℝ)*x 1 + (2457503537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (812894587/1250000000 : ℝ)^5 ≤ (58398981548031/100000000000000 : ℝ)^4 := by
    have hnat : (812894587 : ℕ)^5*100000000000000^4 ≤ 58398981548031^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812894587 1250000000 58398981548031 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66029179/5000000000 : ℝ)^5 ≤ (111917338821/25000000000000 : ℝ)^4 := by
    have hnat : (66029179 : ℕ)^5*25000000000000^4 ≤ 111917338821^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66029179 5000000000 111917338821 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2457503537/5000000000 : ℝ)^5 ≤ (41153349075719/100000000000000 : ℝ)^4 := by
    have hnat : (2457503537 : ℕ)^5*100000000000000^4 ≤ 41153349075719^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457503537 5000000000 41153349075719 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(812894587/1250000000 : ℝ), (-66029179/5000000000 : ℝ), (2457503537/5000000000 : ℝ)] ![(58398981548031/100000000000000 : ℝ), (111917338821/25000000000000 : ℝ), (41153349075719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(812894587/1250000000 : ℝ)|^5 ≤ (58398981548031/100000000000000 : ℝ)^4
        have hw : |(812894587/1250000000 : ℝ)|=(812894587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66029179/5000000000 : ℝ)|^5 ≤ (111917338821/25000000000000 : ℝ)^4
        have hw : |(-66029179/5000000000 : ℝ)|=(66029179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2457503537/5000000000 : ℝ)|^5 ≤ (41153349075719/100000000000000 : ℝ)^4
        have hw : |(2457503537/5000000000 : ℝ)|=(2457503537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3150928959/10000000000 : ℝ)*x 0 + (1779246653/2500000000 : ℝ)*x 1 + (-1713430239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3150928959/10000000000 : ℝ)^5 ≤ (368865714917/1562500000000 : ℝ)^4 := by
    have hnat : (3150928959 : ℕ)^5*1562500000000^4 ≤ 368865714917^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3150928959 10000000000 368865714917 1562500000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1779246653/2500000000 : ℝ)^5 ≤ (32684375431669/50000000000000 : ℝ)^4 := by
    have hnat : (1779246653 : ℕ)^5*50000000000000^4 ≤ 32684375431669^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779246653 2500000000 32684375431669 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1713430239/10000000000 : ℝ)^5 ≤ (11023843368077/100000000000000 : ℝ)^4 := by
    have hnat : (1713430239 : ℕ)^5*100000000000000^4 ≤ 11023843368077^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713430239 10000000000 11023843368077 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3150928959/10000000000 : ℝ), (1779246653/2500000000 : ℝ), (-1713430239/10000000000 : ℝ)] ![(368865714917/1562500000000 : ℝ), (32684375431669/50000000000000 : ℝ), (11023843368077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3150928959/10000000000 : ℝ)|^5 ≤ (368865714917/1562500000000 : ℝ)^4
        have hw : |(3150928959/10000000000 : ℝ)|=(3150928959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1779246653/2500000000 : ℝ)|^5 ≤ (32684375431669/50000000000000 : ℝ)^4
        have hw : |(1779246653/2500000000 : ℝ)|=(1779246653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1713430239/10000000000 : ℝ)|^5 ≤ (11023843368077/100000000000000 : ℝ)^4
        have hw : |(-1713430239/10000000000 : ℝ)|=(1713430239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1368281207/5000000000 : ℝ)*x 0 + (465381801/1000000000 : ℝ)*x 1 + (310859711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368281207/5000000000 : ℝ)^5 ≤ (19792775430729/100000000000000 : ℝ)^4 := by
    have hnat : (1368281207 : ℕ)^5*100000000000000^4 ≤ 19792775430729^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368281207 5000000000 19792775430729 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465381801/1000000000 : ℝ)^5 ≤ (38438085189543/100000000000000 : ℝ)^4 := by
    have hnat : (465381801 : ℕ)^5*100000000000000^4 ≤ 38438085189543^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465381801 1000000000 38438085189543 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310859711/625000000 : ℝ)^5 ≤ (20884569685251/50000000000000 : ℝ)^4 := by
    have hnat : (310859711 : ℕ)^5*50000000000000^4 ≤ 20884569685251^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310859711 625000000 20884569685251 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1368281207/5000000000 : ℝ), (465381801/1000000000 : ℝ), (310859711/625000000 : ℝ)] ![(19792775430729/100000000000000 : ℝ), (38438085189543/100000000000000 : ℝ), (20884569685251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1368281207/5000000000 : ℝ)|^5 ≤ (19792775430729/100000000000000 : ℝ)^4
        have hw : |(1368281207/5000000000 : ℝ)|=(1368281207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465381801/1000000000 : ℝ)|^5 ≤ (38438085189543/100000000000000 : ℝ)^4
        have hw : |(465381801/1000000000 : ℝ)|=(465381801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310859711/625000000 : ℝ)|^5 ≤ (20884569685251/50000000000000 : ℝ)^4
        have hw : |(310859711/625000000 : ℝ)|=(310859711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1590189297/10000000000 : ℝ)*x 0 + (1983283121/5000000000 : ℝ)*x 1 + (6510319533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1590189297/10000000000 : ℝ)^5 ≤ (5020893816821/50000000000000 : ℝ)^4 := by
    have hnat : (1590189297 : ℕ)^5*50000000000000^4 ≤ 5020893816821^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590189297 10000000000 5020893816821 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1983283121/5000000000 : ℝ)^5 ≤ (31478816017877/100000000000000 : ℝ)^4 := by
    have hnat : (1983283121 : ℕ)^5*100000000000000^4 ≤ 31478816017877^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983283121 5000000000 31478816017877 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6510319533/10000000000 : ℝ)^5 ≤ (182748113543/312500000000 : ℝ)^4 := by
    have hnat : (6510319533 : ℕ)^5*312500000000^4 ≤ 182748113543^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6510319533 10000000000 182748113543 312500000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1590189297/10000000000 : ℝ), (1983283121/5000000000 : ℝ), (6510319533/10000000000 : ℝ)] ![(5020893816821/50000000000000 : ℝ), (31478816017877/100000000000000 : ℝ), (182748113543/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1590189297/10000000000 : ℝ)|^5 ≤ (5020893816821/50000000000000 : ℝ)^4
        have hw : |(-1590189297/10000000000 : ℝ)|=(1590189297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1983283121/5000000000 : ℝ)|^5 ≤ (31478816017877/100000000000000 : ℝ)^4
        have hw : |(1983283121/5000000000 : ℝ)|=(1983283121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6510319533/10000000000 : ℝ)|^5 ≤ (182748113543/312500000000 : ℝ)^4
        have hw : |(6510319533/10000000000 : ℝ)|=(6510319533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7559204751/10000000000 : ℝ)*x 0 + (-359412713/5000000000 : ℝ)*x 1 + (845560303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7559204751/10000000000 : ℝ)^5 ≤ (70484745532857/100000000000000 : ℝ)^4 := by
    have hnat : (7559204751 : ℕ)^5*100000000000000^4 ≤ 70484745532857^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7559204751 10000000000 70484745532857 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359412713/5000000000 : ℝ)^5 ≤ (1861012509139/50000000000000 : ℝ)^4 := by
    have hnat : (359412713 : ℕ)^5*50000000000000^4 ≤ 1861012509139^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359412713 5000000000 1861012509139 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845560303/2500000000 : ℝ)^5 ≤ (25793229436081/100000000000000 : ℝ)^4 := by
    have hnat : (845560303 : ℕ)^5*100000000000000^4 ≤ 25793229436081^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845560303 2500000000 25793229436081 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7559204751/10000000000 : ℝ), (-359412713/5000000000 : ℝ), (845560303/2500000000 : ℝ)] ![(70484745532857/100000000000000 : ℝ), (1861012509139/50000000000000 : ℝ), (25793229436081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7559204751/10000000000 : ℝ)|^5 ≤ (70484745532857/100000000000000 : ℝ)^4
        have hw : |(7559204751/10000000000 : ℝ)|=(7559204751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359412713/5000000000 : ℝ)|^5 ≤ (1861012509139/50000000000000 : ℝ)^4
        have hw : |(-359412713/5000000000 : ℝ)|=(359412713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845560303/2500000000 : ℝ)|^5 ≤ (25793229436081/100000000000000 : ℝ)^4
        have hw : |(845560303/2500000000 : ℝ)|=(845560303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (903706937/2500000000 : ℝ)*x 0 + (6770331639/10000000000 : ℝ)*x 1 + (-827601823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903706937/2500000000 : ℝ)^5 ≤ (3503640373281/12500000000000 : ℝ)^4 := by
    have hnat : (903706937 : ℕ)^5*12500000000000^4 ≤ 3503640373281^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903706937 2500000000 3503640373281 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6770331639/10000000000 : ℝ)^5 ≤ (30706649570877/50000000000000 : ℝ)^4 := by
    have hnat : (6770331639 : ℕ)^5*50000000000000^4 ≤ 30706649570877^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6770331639 10000000000 30706649570877 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827601823/5000000000 : ℝ)^5 ≤ (659848616149/6250000000000 : ℝ)^4 := by
    have hnat : (827601823 : ℕ)^5*6250000000000^4 ≤ 659848616149^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827601823 5000000000 659848616149 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(903706937/2500000000 : ℝ), (6770331639/10000000000 : ℝ), (-827601823/5000000000 : ℝ)] ![(3503640373281/12500000000000 : ℝ), (30706649570877/50000000000000 : ℝ), (659848616149/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(903706937/2500000000 : ℝ)|^5 ≤ (3503640373281/12500000000000 : ℝ)^4
        have hw : |(903706937/2500000000 : ℝ)|=(903706937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6770331639/10000000000 : ℝ)|^5 ≤ (30706649570877/50000000000000 : ℝ)^4
        have hw : |(6770331639/10000000000 : ℝ)|=(6770331639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-827601823/5000000000 : ℝ)|^5 ≤ (659848616149/6250000000000 : ℝ)^4
        have hw : |(-827601823/5000000000 : ℝ)|=(827601823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (101256209/400000000 : ℝ)*x 0 + (394154793/1000000000 : ℝ)*x 1 + (1454531623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101256209/400000000 : ℝ)^5 ≤ (17955689644669/100000000000000 : ℝ)^4 := by
    have hnat : (101256209 : ℕ)^5*100000000000000^4 ≤ 17955689644669^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101256209 400000000 17955689644669 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394154793/1000000000 : ℝ)^5 ≤ (15615414594477/50000000000000 : ℝ)^4 := by
    have hnat : (394154793 : ℕ)^5*50000000000000^4 ≤ 15615414594477^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394154793 1000000000 15615414594477 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1454531623/2500000000 : ℝ)^5 ≤ (50813481153027/100000000000000 : ℝ)^4 := by
    have hnat : (1454531623 : ℕ)^5*100000000000000^4 ≤ 50813481153027^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454531623 2500000000 50813481153027 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(101256209/400000000 : ℝ), (394154793/1000000000 : ℝ), (1454531623/2500000000 : ℝ)] ![(17955689644669/100000000000000 : ℝ), (15615414594477/50000000000000 : ℝ), (50813481153027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(101256209/400000000 : ℝ)|^5 ≤ (17955689644669/100000000000000 : ℝ)^4
        have hw : |(101256209/400000000 : ℝ)|=(101256209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(394154793/1000000000 : ℝ)|^5 ≤ (15615414594477/50000000000000 : ℝ)^4
        have hw : |(394154793/1000000000 : ℝ)|=(394154793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1454531623/2500000000 : ℝ)|^5 ≤ (50813481153027/100000000000000 : ℝ)^4
        have hw : |(1454531623/2500000000 : ℝ)|=(1454531623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-868760543/5000000000 : ℝ)*x 0 + (5385612063/10000000000 : ℝ)*x 1 + (5057080493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868760543/5000000000 : ℝ)^5 ≤ (11217926874837/100000000000000 : ℝ)^4 := by
    have hnat : (868760543 : ℕ)^5*100000000000000^4 ≤ 11217926874837^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868760543 5000000000 11217926874837 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385612063/10000000000 : ℝ)^5 ≤ (46136413819841/100000000000000 : ℝ)^4 := by
    have hnat : (5385612063 : ℕ)^5*100000000000000^4 ≤ 46136413819841^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385612063 10000000000 46136413819841 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057080493/10000000000 : ℝ)^5 ≤ (8529131858243/20000000000000 : ℝ)^4 := by
    have hnat : (5057080493 : ℕ)^5*20000000000000^4 ≤ 8529131858243^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057080493 10000000000 8529131858243 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-868760543/5000000000 : ℝ), (5385612063/10000000000 : ℝ), (5057080493/10000000000 : ℝ)] ![(11217926874837/100000000000000 : ℝ), (46136413819841/100000000000000 : ℝ), (8529131858243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-868760543/5000000000 : ℝ)|^5 ≤ (11217926874837/100000000000000 : ℝ)^4
        have hw : |(-868760543/5000000000 : ℝ)|=(868760543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385612063/10000000000 : ℝ)|^5 ≤ (46136413819841/100000000000000 : ℝ)^4
        have hw : |(5385612063/10000000000 : ℝ)|=(5385612063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057080493/10000000000 : ℝ)|^5 ≤ (8529131858243/20000000000000 : ℝ)^4
        have hw : |(5057080493/10000000000 : ℝ)|=(5057080493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1841106469/2500000000 : ℝ)*x 0 + (-126882881/10000000000 : ℝ)*x 1 + (1976902903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841106469/2500000000 : ℝ)^5 ≤ (34110934970433/50000000000000 : ℝ)^4 := by
    have hnat : (1841106469 : ℕ)^5*50000000000000^4 ≤ 34110934970433^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841106469 2500000000 34110934970433 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126882881/10000000000 : ℝ)^5 ≤ (53230899131/12500000000000 : ℝ)^4 := by
    have hnat : (126882881 : ℕ)^5*12500000000000^4 ≤ 53230899131^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126882881 10000000000 53230899131 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1976902903/5000000000 : ℝ)^5 ≤ (6270456569593/20000000000000 : ℝ)^4 := by
    have hnat : (1976902903 : ℕ)^5*20000000000000^4 ≤ 6270456569593^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976902903 5000000000 6270456569593 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1841106469/2500000000 : ℝ), (-126882881/10000000000 : ℝ), (1976902903/5000000000 : ℝ)] ![(34110934970433/50000000000000 : ℝ), (53230899131/12500000000000 : ℝ), (6270456569593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1841106469/2500000000 : ℝ)|^5 ≤ (34110934970433/50000000000000 : ℝ)^4
        have hw : |(1841106469/2500000000 : ℝ)|=(1841106469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126882881/10000000000 : ℝ)|^5 ≤ (53230899131/12500000000000 : ℝ)^4
        have hw : |(-126882881/10000000000 : ℝ)|=(126882881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1976902903/5000000000 : ℝ)|^5 ≤ (6270456569593/20000000000000 : ℝ)^4
        have hw : |(1976902903/5000000000 : ℝ)|=(1976902903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3412979901/10000000000 : ℝ)*x 0 + (6446321873/10000000000 : ℝ)*x 1 + (-465162769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3412979901/10000000000 : ℝ)^5 ≤ (6521645261437/25000000000000 : ℝ)^4 := by
    have hnat : (3412979901 : ℕ)^5*25000000000000^4 ≤ 6521645261437^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3412979901 10000000000 6521645261437 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6446321873/10000000000 : ℝ)^5 ≤ (28880851107323/50000000000000 : ℝ)^4 := by
    have hnat : (6446321873 : ℕ)^5*50000000000000^4 ≤ 28880851107323^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6446321873 10000000000 28880851107323 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465162769/2000000000 : ℝ)^5 ≤ (8075858364733/50000000000000 : ℝ)^4 := by
    have hnat : (465162769 : ℕ)^5*50000000000000^4 ≤ 8075858364733^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465162769 2000000000 8075858364733 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3412979901/10000000000 : ℝ), (6446321873/10000000000 : ℝ), (-465162769/2000000000 : ℝ)] ![(6521645261437/25000000000000 : ℝ), (28880851107323/50000000000000 : ℝ), (8075858364733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3412979901/10000000000 : ℝ)|^5 ≤ (6521645261437/25000000000000 : ℝ)^4
        have hw : |(3412979901/10000000000 : ℝ)|=(3412979901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6446321873/10000000000 : ℝ)|^5 ≤ (28880851107323/50000000000000 : ℝ)^4
        have hw : |(6446321873/10000000000 : ℝ)|=(6446321873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-465162769/2000000000 : ℝ)|^5 ≤ (8075858364733/50000000000000 : ℝ)^4
        have hw : |(-465162769/2000000000 : ℝ)|=(465162769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319083_s1_s1_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1602484743/5000000000 : ℝ)*x 0 + (941502509/2000000000 : ℝ)*x 1 + (2251735321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1602484743/5000000000 : ℝ)^5 ≤ (6028647380683/25000000000000 : ℝ)^4 := by
    have hnat : (1602484743 : ℕ)^5*25000000000000^4 ≤ 6028647380683^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602484743 5000000000 6028647380683 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941502509/2000000000 : ℝ)^5 ≤ (2437077695029/6250000000000 : ℝ)^4 := by
    have hnat : (941502509 : ℕ)^5*6250000000000^4 ≤ 2437077695029^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941502509 2000000000 2437077695029 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251735321/5000000000 : ℝ)^5 ≤ (18446083670977/50000000000000 : ℝ)^4 := by
    have hnat : (2251735321 : ℕ)^5*50000000000000^4 ≤ 18446083670977^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251735321 5000000000 18446083670977 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1602484743/5000000000 : ℝ), (941502509/2000000000 : ℝ), (2251735321/5000000000 : ℝ)] ![(6028647380683/25000000000000 : ℝ), (2437077695029/6250000000000 : ℝ), (18446083670977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1602484743/5000000000 : ℝ)|^5 ≤ (6028647380683/25000000000000 : ℝ)^4
        have hw : |(1602484743/5000000000 : ℝ)|=(1602484743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(941502509/2000000000 : ℝ)|^5 ≤ (2437077695029/6250000000000 : ℝ)^4
        have hw : |(941502509/2000000000 : ℝ)|=(941502509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251735321/5000000000 : ℝ)|^5 ≤ (18446083670977/50000000000000 : ℝ)^4
        have hw : |(2251735321/5000000000 : ℝ)|=(2251735321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319083_s1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4039/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4039/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((31723/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(31723/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35173/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35173/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6031/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6031/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((24721/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(24721/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12789/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12789/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (4039/6250 : ℝ) ^ (79/16 : ℝ) ≤ (289574005210420827/2500000000000000000 : ℝ) := by
    have hpowers : (4039/6250 : ℝ)^79 ≤ (289574005210420827/2500000000000000000 : ℝ)^16 := by
      have hnat : (4039 : ℕ)^79*2500000000000000000^16 ≤ 289574005210420827^16*6250^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4039 6250 289574005210420827 2500000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4039/6250 : ℝ)) (X := (289574005210420827/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (2789574005210420827/2500000000000000000 : ℝ) ≤ (1278056606774193/1250000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2789574005210420827/2500000000000000000 : ℝ)^16 ≤ (1278056606774193/1250000000000000 : ℝ)^79 := by
      have hnat : (2789574005210420827 : ℕ)^16*1250000000000000^79 ≤ 1278056606774193^79*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2789574005210420827 2500000000000000000 1278056606774193 1250000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1278056606774193/1250000000000000 : ℝ)) (X := (2789574005210420827/2500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1539574005210420827/1250000000000000000 : ℝ) ≤ (521551508287443/500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (1539574005210420827/1250000000000000000 : ℝ)^16 ≤ (521551508287443/500000000000000 : ℝ)^79 := by
      have hnat : (1539574005210420827 : ℕ)^16*500000000000000^79 ≤ 521551508287443^79*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1539574005210420827 1250000000000000000 521551508287443 500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (521551508287443/500000000000000 : ℝ)) (X := (1539574005210420827/1250000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(28056606774193/807800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(51644327888829/1615600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (4039/6250 : ℝ)) (alpha := (28056606774193/807800000000000 : ℝ)) (beta := (51644327888829/1615600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4039/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(28056606774193/807800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(51644327888829/1615600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (31723/50000 : ℝ) ^ (79/16 : ℝ) ≤ (10577206152662930267/100000000000000000000 : ℝ) := by
    have hpowers : (31723/50000 : ℝ)^79 ≤ (10577206152662930267/100000000000000000000 : ℝ)^16 := by
      have hnat : (31723 : ℕ)^79*100000000000000000000^16 ≤ 10577206152662930267^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31723 50000 10577206152662930267 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31723/50000 : ℝ)) (X := (10577206152662930267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (110577206152662930267/100000000000000000000 : ℝ) ≤ (1020572045569499/1000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (110577206152662930267/100000000000000000000 : ℝ)^16 ≤ (1020572045569499/1000000000000000 : ℝ)^79 := by
      have hnat : (110577206152662930267 : ℕ)^16*1000000000000000^79 ≤ 1020572045569499^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110577206152662930267 100000000000000000000 1020572045569499 1000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1020572045569499/1000000000000000 : ℝ)) (X := (110577206152662930267/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (60577206152662930267/50000000000000000000 : ℝ) ≤ (2599075175145421/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (60577206152662930267/50000000000000000000 : ℝ)^16 ≤ (2599075175145421/2500000000000000 : ℝ)^79 := by
      have hnat : (60577206152662930267 : ℕ)^16*2500000000000000^79 ≤ 2599075175145421^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60577206152662930267 50000000000000000000 2599075175145421 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2599075175145421/2500000000000000 : ℝ)) (X := (60577206152662930267/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(20572045569499/634460000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(95290122443347/3172300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (31723/50000 : ℝ)) (alpha := (20572045569499/634460000000000 : ℝ)) (beta := (95290122443347/3172300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (31723/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(20572045569499/634460000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(95290122443347/3172300000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (35173/50000 : ℝ) ^ (79/16 : ℝ) ≤ (17609400686433678391/100000000000000000000 : ℝ) := by
    have hpowers : (35173/50000 : ℝ)^79 ≤ (17609400686433678391/100000000000000000000 : ℝ)^16 := by
      have hnat : (35173 : ℕ)^79*100000000000000000000^16 ≤ 17609400686433678391^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35173 50000 17609400686433678391 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35173/50000 : ℝ)) (X := (17609400686433678391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (117609400686433678391/100000000000000000000 : ℝ) ≤ (10333959178512039/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (117609400686433678391/100000000000000000000 : ℝ)^16 ≤ (10333959178512039/10000000000000000 : ℝ)^79 := by
      have hnat : (117609400686433678391 : ℕ)^16*10000000000000000^79 ≤ 10333959178512039^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117609400686433678391 100000000000000000000 10333959178512039 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10333959178512039/10000000000000000 : ℝ)) (X := (117609400686433678391/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (67609400686433678391/50000000000000000000 : ℝ) ≤ (5315072099631513/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (67609400686433678391/50000000000000000000 : ℝ)^16 ≤ (5315072099631513/5000000000000000 : ℝ)^79 := by
      have hnat : (67609400686433678391 : ℕ)^16*5000000000000000^79 ≤ 5315072099631513^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67609400686433678391 50000000000000000000 5315072099631513 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5315072099631513/5000000000000000 : ℝ)) (X := (67609400686433678391/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(333959178512039/7034600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(296185020750987/7034600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (35173/50000 : ℝ)) (alpha := (333959178512039/7034600000000000 : ℝ)) (beta := (296185020750987/7034600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35173/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(333959178512039/7034600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(296185020750987/7034600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1142614289/5000000000 : ℝ)*X 0 0+(596239083/1250000000 : ℝ)*X 0 1+(40920567/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1678354303/2500000000 : ℝ)*X 1 0+(-855217093/10000000000 : ℝ)*X 1 1+(2139421907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3547381337/10000000000 : ℝ)*X 2 0+(6337028871/10000000000 : ℝ)*X 2 1+(-2317882197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2340783757/10000000000 : ℝ)*X 0 0+(4729644427/10000000000 : ℝ)*X 0 1+(2615919831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((812894587/1250000000 : ℝ)*X 1 0+(-66029179/5000000000 : ℝ)*X 1 1+(2457503537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3150928959/10000000000 : ℝ)*X 2 0+(1779246653/2500000000 : ℝ)*X 2 1+(-1713430239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1368281207/5000000000 : ℝ)*X 0 0+(465381801/1000000000 : ℝ)*X 0 1+(310859711/625000000 : ℝ)*X 0 2+(1368281207/5000000000 : ℝ)*X 1 0+(465381801/1000000000 : ℝ)*X 1 1+(310859711/625000000 : ℝ)*X 1 2+(1368281207/5000000000 : ℝ)*X 2 0+(465381801/1000000000 : ℝ)*X 2 1+(310859711/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1590189297/10000000000 : ℝ)*X 0 0+(1983283121/5000000000 : ℝ)*X 0 1+(6510319533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7559204751/10000000000 : ℝ)*X 1 0+(-359412713/5000000000 : ℝ)*X 1 1+(845560303/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((903706937/2500000000 : ℝ)*X 2 0+(6770331639/10000000000 : ℝ)*X 2 1+(-827601823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((101256209/400000000 : ℝ)*X 0 0+(394154793/1000000000 : ℝ)*X 0 1+(1454531623/2500000000 : ℝ)*X 0 2+(101256209/400000000 : ℝ)*X 1 0+(394154793/1000000000 : ℝ)*X 1 1+(1454531623/2500000000 : ℝ)*X 1 2+(101256209/400000000 : ℝ)*X 2 0+(394154793/1000000000 : ℝ)*X 2 1+(1454531623/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-868760543/5000000000 : ℝ)*X 0 0+(5385612063/10000000000 : ℝ)*X 0 1+(5057080493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1841106469/2500000000 : ℝ)*X 1 0+(-126882881/10000000000 : ℝ)*X 1 1+(1976902903/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3412979901/10000000000 : ℝ)*X 2 0+(6446321873/10000000000 : ℝ)*X 2 1+(-465162769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1602484743/5000000000 : ℝ)*X 0 0+(941502509/2000000000 : ℝ)*X 0 1+(2251735321/5000000000 : ℝ)*X 0 2+(1602484743/5000000000 : ℝ)*X 1 0+(941502509/2000000000 : ℝ)*X 1 1+(2251735321/5000000000 : ℝ)*X 1 2+(1602484743/5000000000 : ℝ)*X 2 0+(941502509/2000000000 : ℝ)*X 2 1+(2251735321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((6031/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6031/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31646850967908398744462901057/4023828791143750000000000000000000 : ℝ) := by norm_num
    linear_combination (774173/125000000000 : ℝ)*(base19) + (109129859929/500000000000 : ℝ)*(base40) + (1485009429013/1000000000000 : ℝ)*(base49) + (238972379103/500000000000 : ℝ)*(base60) + (1191624440013/250000000000 : ℝ)*(major_s1_0) + (1191624440013/250000000000 : ℝ)*(major_s1_1) + (1191624440013/250000000000 : ℝ)*(major_s1_2) + (622735727/1000000000000 : ℝ)*(sp_s1_0) + (22872453/1000000000000 : ℝ)*(sp_s1_1) + (6957193355261/1000000000000 : ℝ)*(sp_s1_7) + (139155740503/20000000000 : ℝ)*(sp_s1_8) + (1739454022747/250000000000 : ℝ)*(sp_s1_9) + (103006643307/40000000000 : ℝ)*(sp_s1_13) + (5362407/500000000000 : ℝ)*(sp_s1_20) + (40237137617/15625000000 : ℝ)*(f.failure) + (1739454022747/250000000000 : ℝ)*(f.sum) + (71045913432096753/174342668593750000000000000000 : ℝ)*base62 + (755594215509797/879325000000000000000000000 : ℝ)*base64 + (68442069962583/79307500000000000000000000 : ℝ)*base66 + (38231315554633/1758650000000000000000000000 : ℝ)*base68 + (536185439705897167/1014741050000000000000000000000 : ℝ)*base70 + (15839653347989/57700000000000000000000000 : ℝ)*base72 + (737496491729801/793075000000000000000000000 : ℝ)*base74 + (25638154371223/28850000000000000000000000 : ℝ)*base76 + (639162422253069527/1830417100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (63/390625000000000 : ℝ)*base86 + (63/390625000000000 : ℝ)*base88 + (63/390625000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((24721/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(24721/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2345173350692463703575393634923/180267529843240000000000000000000000 : ℝ) := by norm_num
    linear_combination (1798697/250000000000 : ℝ)*(base8) + (756243/500000000000 : ℝ)*(base21) + (482074763253/500000000000 : ℝ)*(base40) + (1315574945441/1000000000000 : ℝ)*(base49) + (6483411443/7812500000 : ℝ)*(base60) + (172235003551/40000000000 : ℝ)*(major_s1_0) + (172235003551/40000000000 : ℝ)*(major_s1_1) + (172235003551/40000000000 : ℝ)*(major_s1_2) + (107753531/1000000000000 : ℝ)*(sp_s1_2) + (1257084123871/200000000000 : ℝ)*(sp_s1_14) + (24552263241/3906250000 : ℝ)*(sp_s1_15) + (10056509677/1600000000 : ℝ)*(sp_s1_16) + (465263605387/200000000000 : ℝ)*(sp_s1_20) + (48424447/1000000000000 : ℝ)*(sp_s1_22) + (465263605387/200000000000 : ℝ)*(f.failure) + (6285427814143/1000000000000 : ℝ)*(f.sum) + (546776442377912223/8926344632000000000000000000000 : ℝ)*base62 + (154207404983973/281384000000000000000000000 : ℝ)*base65 + (789616541183/126892000000000000000000000 : ℝ)*base67 + (970565934544511/1406920000000000000000000000 : ℝ)*base68 + (841805677411955937/2841274940000000000000000000000 : ℝ)*base71 + (36353083740447/323120000000000000000000000 : ℝ)*base73 + (362538979553403/634460000000000000000000000 : ℝ)*base75 + (25040578852259/161560000000000000000000000 : ℝ)*base77 + (728037644432106297/10250335760000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (689/10000000000000000 : ℝ)*base87 + (689/10000000000000000 : ℝ)*base89 + (689/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12789/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12789/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2906277000847728168279842048811/450668824608100000000000000000000000 : ℝ) := by norm_num
    linear_combination (50418188891/62500000000 : ℝ)*(base40) + (1499976172003/1000000000000 : ℝ)*(base49) + (21089/8000000000 : ℝ)*(base50) + (8123983227/1000000000000 : ℝ)*(base60) + (5023292203403/1000000000000 : ℝ)*(major_s1_0) + (5023292203403/1000000000000 : ℝ)*(major_s1_1) + (5023292203403/1000000000000 : ℝ)*(major_s1_2) + (85990077/1000000000000 : ℝ)*(sp_s1_2) + (33609047/1000000000000 : ℝ)*(sp_s1_15) + (10633417/250000000000 : ℝ)*(sp_s1_16) + (458291758503/62500000000 : ℝ)*(sp_s1_21) + (7332634527001/1000000000000 : ℝ)*(sp_s1_22) + (7332539612303/1000000000000 : ℝ)*(sp_s1_23) + (2713914121151/1000000000000 : ℝ)*(sp_s1_27) + (2713914121151/1000000000000 : ℝ)*(f.failure) + (458291758503/62500000000 : ℝ)*(f.sum) + (56504044201888170647/44631723160000000000000000000000 : ℝ)*base62 + (4096980243045021/7034600000000000000000000000 : ℝ)*base65 + (102957652003179/634460000000000000000000000 : ℝ)*base66 + (2125467373645423/7034600000000000000000000000 : ℝ)*base68 + (5276911359297101483/14206374700000000000000000000000 : ℝ)*base71 + (261339417294367/1615600000000000000000000000 : ℝ)*base73 + (1859131890334301/3172300000000000000000000000 : ℝ)*base74 + (86216661907039/807800000000000000000000000 : ℝ)*base77 + (18242724807827984239/51251678800000000000000000000000 : ℝ)*base78 + (11597/50000000000000000 : ℝ)*base87 + (11597/50000000000000000 : ℝ)*base89 + (11597/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4039/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4039/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((31723/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(31723/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35173/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35173/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6031/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6031/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((24721/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(24721/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12789/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12789/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c319083_s1 p hpa hpb X hX hprev0

#print axioms solution
