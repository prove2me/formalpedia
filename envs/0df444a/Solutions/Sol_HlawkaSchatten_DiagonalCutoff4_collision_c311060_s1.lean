-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:00:39.514983+00:00
-- url     : https://prove2.me/submissions/94163106-0ecf-4c25-8790-49428d22aa97

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
theorem collision_support_c311060_s1_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-417962523/2500000000 : ℝ)*x 0 + (4471605397/10000000000 : ℝ)*x 1 + (-3115870519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417962523/2500000000 : ℝ)^9 ≤ (10028909548803/100000000000000 : ℝ)^7 := by
    have hnat : (417962523 : ℕ)^9*100000000000000^7 ≤ 10028909548803^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417962523 2500000000 10028909548803 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4471605397/10000000000 : ℝ)^9 ≤ (277578562583/781250000000 : ℝ)^7 := by
    have hnat : (4471605397 : ℕ)^9*781250000000^7 ≤ 277578562583^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471605397 10000000000 277578562583 781250000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3115870519/5000000000 : ℝ)^9 ≤ (54441034428031/100000000000000 : ℝ)^7 := by
    have hnat : (3115870519 : ℕ)^9*100000000000000^7 ≤ 54441034428031^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115870519 5000000000 54441034428031 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417962523/2500000000 : ℝ), (4471605397/10000000000 : ℝ), (-3115870519/5000000000 : ℝ)] ![(10028909548803/100000000000000 : ℝ), (277578562583/781250000000 : ℝ), (54441034428031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417962523/2500000000 : ℝ)|^9 ≤ (10028909548803/100000000000000 : ℝ)^7
        have hw : |(-417962523/2500000000 : ℝ)|=(417962523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4471605397/10000000000 : ℝ)|^9 ≤ (277578562583/781250000000 : ℝ)^7
        have hw : |(4471605397/10000000000 : ℝ)|=(4471605397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3115870519/5000000000 : ℝ)|^9 ≤ (54441034428031/100000000000000 : ℝ)^7
        have hw : |(-3115870519/5000000000 : ℝ)|=(3115870519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2256728227/5000000000 : ℝ)*x 0 + (-426900887/2500000000 : ℝ)*x 1 + (-246756397/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256728227/5000000000 : ℝ)^9 ≤ (35958172855257/100000000000000 : ℝ)^7 := by
    have hnat : (2256728227 : ℕ)^9*100000000000000^7 ≤ 35958172855257^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256728227 5000000000 35958172855257 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426900887/2500000000 : ℝ)^9 ≤ (1288187484337/12500000000000 : ℝ)^7 := by
    have hnat : (426900887 : ℕ)^9*12500000000000^7 ≤ 1288187484337^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426900887 2500000000 1288187484337 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246756397/400000000 : ℝ)^9 ≤ (53736327247239/100000000000000 : ℝ)^7 := by
    have hnat : (246756397 : ℕ)^9*100000000000000^7 ≤ 53736327247239^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246756397 400000000 53736327247239 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256728227/5000000000 : ℝ), (-426900887/2500000000 : ℝ), (-246756397/400000000 : ℝ)] ![(35958172855257/100000000000000 : ℝ), (1288187484337/12500000000000 : ℝ), (53736327247239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256728227/5000000000 : ℝ)|^9 ≤ (35958172855257/100000000000000 : ℝ)^7
        have hw : |(2256728227/5000000000 : ℝ)|=(2256728227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426900887/2500000000 : ℝ)|^9 ≤ (1288187484337/12500000000000 : ℝ)^7
        have hw : |(-426900887/2500000000 : ℝ)|=(426900887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246756397/400000000 : ℝ)|^9 ≤ (53736327247239/100000000000000 : ℝ)^7
        have hw : |(-246756397/400000000 : ℝ)|=(246756397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-971473467/5000000000 : ℝ)*x 0 + (2527211739/10000000000 : ℝ)*x 1 + (-3821246611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971473467/5000000000 : ℝ)^9 ≤ (12166455297631/100000000000000 : ℝ)^7 := by
    have hnat : (971473467 : ℕ)^9*100000000000000^7 ≤ 12166455297631^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971473467 5000000000 12166455297631 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2527211739/10000000000 : ℝ)^9 ≤ (8529779697969/50000000000000 : ℝ)^7 := by
    have hnat : (2527211739 : ℕ)^9*50000000000000^7 ≤ 8529779697969^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527211739 10000000000 8529779697969 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3821246611/5000000000 : ℝ)^9 ≤ (70773985286723/100000000000000 : ℝ)^7 := by
    have hnat : (3821246611 : ℕ)^9*100000000000000^7 ≤ 70773985286723^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3821246611 5000000000 70773985286723 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-971473467/5000000000 : ℝ), (2527211739/10000000000 : ℝ), (-3821246611/5000000000 : ℝ)] ![(12166455297631/100000000000000 : ℝ), (8529779697969/50000000000000 : ℝ), (70773985286723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-971473467/5000000000 : ℝ)|^9 ≤ (12166455297631/100000000000000 : ℝ)^7
        have hw : |(-971473467/5000000000 : ℝ)|=(971473467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2527211739/10000000000 : ℝ)|^9 ≤ (8529779697969/50000000000000 : ℝ)^7
        have hw : |(2527211739/10000000000 : ℝ)|=(2527211739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3821246611/5000000000 : ℝ)|^9 ≤ (70773985286723/100000000000000 : ℝ)^7
        have hw : |(-3821246611/5000000000 : ℝ)|=(3821246611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3002304897/10000000000 : ℝ)*x 0 + (-1399839453/10000000000 : ℝ)*x 1 + (-3819364109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3002304897/10000000000 : ℝ)^9 ≤ (21289044242581/100000000000000 : ℝ)^7 := by
    have hnat : (3002304897 : ℕ)^9*100000000000000^7 ≤ 21289044242581^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3002304897 10000000000 21289044242581 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1399839453/10000000000 : ℝ)^9 ≤ (249431100269/3125000000000 : ℝ)^7 := by
    have hnat : (1399839453 : ℕ)^9*3125000000000^7 ≤ 249431100269^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399839453 10000000000 249431100269 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3819364109/5000000000 : ℝ)^9 ≤ (14145832106201/20000000000000 : ℝ)^7 := by
    have hnat : (3819364109 : ℕ)^9*20000000000000^7 ≤ 14145832106201^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3819364109 5000000000 14145832106201 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3002304897/10000000000 : ℝ), (-1399839453/10000000000 : ℝ), (-3819364109/5000000000 : ℝ)] ![(21289044242581/100000000000000 : ℝ), (249431100269/3125000000000 : ℝ), (14145832106201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3002304897/10000000000 : ℝ)|^9 ≤ (21289044242581/100000000000000 : ℝ)^7
        have hw : |(3002304897/10000000000 : ℝ)|=(3002304897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1399839453/10000000000 : ℝ)|^9 ≤ (249431100269/3125000000000 : ℝ)^7
        have hw : |(-1399839453/10000000000 : ℝ)|=(1399839453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3819364109/5000000000 : ℝ)|^9 ≤ (14145832106201/20000000000000 : ℝ)^7
        have hw : |(-3819364109/5000000000 : ℝ)|=(3819364109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3173166777/10000000000 : ℝ)*x 0 + (7458213629/10000000000 : ℝ)*x 1 + (738594337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3173166777/10000000000 : ℝ)^9 ≤ (22859266888511/100000000000000 : ℝ)^7 := by
    have hnat : (3173166777 : ℕ)^9*100000000000000^7 ≤ 22859266888511^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173166777 10000000000 22859266888511 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7458213629/10000000000 : ℝ)^9 ≤ (68587467458801/100000000000000 : ℝ)^7 := by
    have hnat : (7458213629 : ℕ)^9*100000000000000^7 ≤ 68587467458801^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7458213629 10000000000 68587467458801 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738594337/5000000000 : ℝ)^9 ≤ (53457910267/625000000000 : ℝ)^7 := by
    have hnat : (738594337 : ℕ)^9*625000000000^7 ≤ 53457910267^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738594337 5000000000 53457910267 625000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3173166777/10000000000 : ℝ), (7458213629/10000000000 : ℝ), (738594337/5000000000 : ℝ)] ![(22859266888511/100000000000000 : ℝ), (68587467458801/100000000000000 : ℝ), (53457910267/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3173166777/10000000000 : ℝ)|^9 ≤ (22859266888511/100000000000000 : ℝ)^7
        have hw : |(3173166777/10000000000 : ℝ)|=(3173166777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7458213629/10000000000 : ℝ)|^9 ≤ (68587467458801/100000000000000 : ℝ)^7
        have hw : |(7458213629/10000000000 : ℝ)|=(7458213629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738594337/5000000000 : ℝ)|^9 ≤ (53457910267/625000000000 : ℝ)^7
        have hw : |(738594337/5000000000 : ℝ)|=(738594337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4805648893/10000000000 : ℝ)*x 0 + (1702525273/2500000000 : ℝ)*x 1 + (-28481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4805648893/10000000000 : ℝ)^9 ≤ (3897840360389/10000000000000 : ℝ)^7 := by
    have hnat : (4805648893 : ℕ)^9*10000000000000^7 ≤ 3897840360389^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805648893 10000000000 3897840360389 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1702525273/2500000000 : ℝ)^9 ≤ (3813846103447/6250000000000 : ℝ)^7 := by
    have hnat : (1702525273 : ℕ)^9*6250000000000^7 ≤ 3813846103447^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702525273 2500000000 3813846103447 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28481/2000000000 : ℝ)^9 ≤ (58724343/100000000000000 : ℝ)^7 := by
    have hnat : (28481 : ℕ)^9*100000000000000^7 ≤ 58724343^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28481 2000000000 58724343 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4805648893/10000000000 : ℝ), (1702525273/2500000000 : ℝ), (-28481/2000000000 : ℝ)] ![(3897840360389/10000000000000 : ℝ), (3813846103447/6250000000000 : ℝ), (58724343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4805648893/10000000000 : ℝ)|^9 ≤ (3897840360389/10000000000000 : ℝ)^7
        have hw : |(4805648893/10000000000 : ℝ)|=(4805648893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1702525273/2500000000 : ℝ)|^9 ≤ (3813846103447/6250000000000 : ℝ)^7
        have hw : |(1702525273/2500000000 : ℝ)|=(1702525273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28481/2000000000 : ℝ)|^9 ≤ (58724343/100000000000000 : ℝ)^7
        have hw : |(-28481/2000000000 : ℝ)|=(28481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1432498027/10000000000 : ℝ)*x 0 + (2655076159/10000000000 : ℝ)*x 1 + (-1969717959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1432498027/10000000000 : ℝ)^9 ≤ (1644402155641/20000000000000 : ℝ)^7 := by
    have hnat : (1432498027 : ℕ)^9*20000000000000^7 ≤ 1644402155641^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1432498027 10000000000 1644402155641 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2655076159/10000000000 : ℝ)^9 ≤ (18177223602359/100000000000000 : ℝ)^7 := by
    have hnat : (2655076159 : ℕ)^9*100000000000000^7 ≤ 18177223602359^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655076159 10000000000 18177223602359 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1969717959/2500000000 : ℝ)^9 ≤ (36800382802037/50000000000000 : ℝ)^7 := by
    have hnat : (1969717959 : ℕ)^9*50000000000000^7 ≤ 36800382802037^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969717959 2500000000 36800382802037 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1432498027/10000000000 : ℝ), (2655076159/10000000000 : ℝ), (-1969717959/2500000000 : ℝ)] ![(1644402155641/20000000000000 : ℝ), (18177223602359/100000000000000 : ℝ), (36800382802037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1432498027/10000000000 : ℝ)|^9 ≤ (1644402155641/20000000000000 : ℝ)^7
        have hw : |(-1432498027/10000000000 : ℝ)|=(1432498027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2655076159/10000000000 : ℝ)|^9 ≤ (18177223602359/100000000000000 : ℝ)^7
        have hw : |(2655076159/10000000000 : ℝ)|=(2655076159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1969717959/2500000000 : ℝ)|^9 ≤ (36800382802037/50000000000000 : ℝ)^7
        have hw : |(-1969717959/2500000000 : ℝ)|=(1969717959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2109487261/10000000000 : ℝ)*x 0 + (-101811303/500000000 : ℝ)*x 1 + (-984373333/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109487261/10000000000 : ℝ)^9 ≤ (13523359546117/100000000000000 : ℝ)^7 := by
    have hnat : (2109487261 : ℕ)^9*100000000000000^7 ≤ 13523359546117^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109487261 10000000000 13523359546117 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101811303/500000000 : ℝ)^9 ≤ (315491567/2441406250 : ℝ)^7 := by
    have hnat : (101811303 : ℕ)^9*2441406250^7 ≤ 315491567^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101811303 500000000 315491567 2441406250 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (984373333/1250000000 : ℝ)^9 ≤ (73554105853039/100000000000000 : ℝ)^7 := by
    have hnat : (984373333 : ℕ)^9*100000000000000^7 ≤ 73554105853039^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984373333 1250000000 73554105853039 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109487261/10000000000 : ℝ), (-101811303/500000000 : ℝ), (-984373333/1250000000 : ℝ)] ![(13523359546117/100000000000000 : ℝ), (315491567/2441406250 : ℝ), (73554105853039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109487261/10000000000 : ℝ)|^9 ≤ (13523359546117/100000000000000 : ℝ)^7
        have hw : |(2109487261/10000000000 : ℝ)|=(2109487261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101811303/500000000 : ℝ)|^9 ≤ (315491567/2441406250 : ℝ)^7
        have hw : |(-101811303/500000000 : ℝ)|=(101811303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-984373333/1250000000 : ℝ)|^9 ≤ (73554105853039/100000000000000 : ℝ)^7
        have hw : |(-984373333/1250000000 : ℝ)|=(984373333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1287490971/2000000000 : ℝ)*x 0 + (4329988609/10000000000 : ℝ)*x 1 + (311285907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1287490971/2000000000 : ℝ)^9 ≤ (7095305879417/12500000000000 : ℝ)^7 := by
    have hnat : (1287490971 : ℕ)^9*12500000000000^7 ≤ 7095305879417^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287490971 2000000000 7095305879417 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4329988609/10000000000 : ℝ)^9 ≤ (34089907779743/100000000000000 : ℝ)^7 := by
    have hnat : (4329988609 : ℕ)^9*100000000000000^7 ≤ 34089907779743^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329988609 10000000000 34089907779743 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311285907/2000000000 : ℝ)^9 ≤ (365905806643/4000000000000 : ℝ)^7 := by
    have hnat : (311285907 : ℕ)^9*4000000000000^7 ≤ 365905806643^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311285907 2000000000 365905806643 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1287490971/2000000000 : ℝ), (4329988609/10000000000 : ℝ), (311285907/2000000000 : ℝ)] ![(7095305879417/12500000000000 : ℝ), (34089907779743/100000000000000 : ℝ), (365905806643/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1287490971/2000000000 : ℝ)|^9 ≤ (7095305879417/12500000000000 : ℝ)^7
        have hw : |(1287490971/2000000000 : ℝ)|=(1287490971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4329988609/10000000000 : ℝ)|^9 ≤ (34089907779743/100000000000000 : ℝ)^7
        have hw : |(4329988609/10000000000 : ℝ)|=(4329988609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311285907/2000000000 : ℝ)|^9 ≤ (365905806643/4000000000000 : ℝ)^7
        have hw : |(311285907/2000000000 : ℝ)|=(311285907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8445775637/10000000000 : ℝ)*x 0 + (2806384639/10000000000 : ℝ)*x 1 + (-408727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8445775637/10000000000 : ℝ)^9 ≤ (80478413941747/100000000000000 : ℝ)^7 := by
    have hnat : (8445775637 : ℕ)^9*100000000000000^7 ≤ 80478413941747^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8445775637 10000000000 80478413941747 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2806384639/10000000000 : ℝ)^9 ≤ (3903956411893/20000000000000 : ℝ)^7 := by
    have hnat : (2806384639 : ℕ)^9*20000000000000^7 ≤ 3903956411893^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806384639 10000000000 3903956411893 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408727/2000000000 : ℝ)^9 ≤ (1803984723/100000000000000 : ℝ)^7 := by
    have hnat : (408727 : ℕ)^9*100000000000000^7 ≤ 1803984723^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408727 2000000000 1803984723 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8445775637/10000000000 : ℝ), (2806384639/10000000000 : ℝ), (-408727/2000000000 : ℝ)] ![(80478413941747/100000000000000 : ℝ), (3903956411893/20000000000000 : ℝ), (1803984723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8445775637/10000000000 : ℝ)|^9 ≤ (80478413941747/100000000000000 : ℝ)^7
        have hw : |(8445775637/10000000000 : ℝ)|=(8445775637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2806384639/10000000000 : ℝ)|^9 ≤ (3903956411893/20000000000000 : ℝ)^7
        have hw : |(2806384639/10000000000 : ℝ)|=(2806384639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408727/2000000000 : ℝ)|^9 ≤ (1803984723/100000000000000 : ℝ)^7
        have hw : |(-408727/2000000000 : ℝ)|=(408727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-469855951/5000000000 : ℝ)*x 0 + (1213798211/2000000000 : ℝ)*x 1 + (-1287336589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469855951/5000000000 : ℝ)^9 ≤ (149422043419/3125000000000 : ℝ)^7 := by
    have hnat : (469855951 : ℕ)^9*3125000000000^7 ≤ 149422043419^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469855951 5000000000 149422043419 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213798211/2000000000 : ℝ)^9 ≤ (6577483924991/12500000000000 : ℝ)^7 := by
    have hnat : (1213798211 : ℕ)^9*12500000000000^7 ≤ 6577483924991^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213798211 2000000000 6577483924991 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287336589/2500000000 : ℝ)^9 ≤ (21299311598599/50000000000000 : ℝ)^7 := by
    have hnat : (1287336589 : ℕ)^9*50000000000000^7 ≤ 21299311598599^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287336589 2500000000 21299311598599 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469855951/5000000000 : ℝ), (1213798211/2000000000 : ℝ), (-1287336589/2500000000 : ℝ)] ![(149422043419/3125000000000 : ℝ), (6577483924991/12500000000000 : ℝ), (21299311598599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469855951/5000000000 : ℝ)|^9 ≤ (149422043419/3125000000000 : ℝ)^7
        have hw : |(-469855951/5000000000 : ℝ)|=(469855951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1213798211/2000000000 : ℝ)|^9 ≤ (6577483924991/12500000000000 : ℝ)^7
        have hw : |(1213798211/2000000000 : ℝ)|=(1213798211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1287336589/2500000000 : ℝ)|^9 ≤ (21299311598599/50000000000000 : ℝ)^7
        have hw : |(-1287336589/2500000000 : ℝ)|=(1287336589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6252532699/10000000000 : ℝ)*x 0 + (-1116176829/10000000000 : ℝ)*x 1 + (-4842171199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6252532699/10000000000 : ℝ)^9 ≤ (27337339961147/50000000000000 : ℝ)^7 := by
    have hnat : (6252532699 : ℕ)^9*50000000000000^7 ≤ 27337339961147^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6252532699 10000000000 27337339961147 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116176829/10000000000 : ℝ)^9 ≤ (5965635544197/100000000000000 : ℝ)^7 := by
    have hnat : (1116176829 : ℕ)^9*100000000000000^7 ≤ 5965635544197^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116176829 10000000000 5965635544197 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4842171199/10000000000 : ℝ)^9 ≤ (19679842263897/50000000000000 : ℝ)^7 := by
    have hnat : (4842171199 : ℕ)^9*50000000000000^7 ≤ 19679842263897^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842171199 10000000000 19679842263897 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6252532699/10000000000 : ℝ), (-1116176829/10000000000 : ℝ), (-4842171199/10000000000 : ℝ)] ![(27337339961147/50000000000000 : ℝ), (5965635544197/100000000000000 : ℝ), (19679842263897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6252532699/10000000000 : ℝ)|^9 ≤ (27337339961147/50000000000000 : ℝ)^7
        have hw : |(6252532699/10000000000 : ℝ)|=(6252532699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1116176829/10000000000 : ℝ)|^9 ≤ (5965635544197/100000000000000 : ℝ)^7
        have hw : |(-1116176829/10000000000 : ℝ)|=(1116176829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4842171199/10000000000 : ℝ)|^9 ≤ (19679842263897/50000000000000 : ℝ)^7
        have hw : |(-4842171199/10000000000 : ℝ)|=(4842171199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (53049741/200000000 : ℝ)*x 0 + (119510037/156250000 : ℝ)*x 1 + (898123411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53049741/200000000 : ℝ)^9 ≤ (18154436723081/100000000000000 : ℝ)^7 := by
    have hnat : (53049741 : ℕ)^9*100000000000000^7 ≤ 18154436723081^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53049741 200000000 18154436723081 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119510037/156250000 : ℝ)^9 ≤ (17711802082287/25000000000000 : ℝ)^7 := by
    have hnat : (119510037 : ℕ)^9*25000000000000^7 ≤ 17711802082287^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119510037 156250000 17711802082287 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898123411/5000000000 : ℝ)^9 ≤ (10998354928287/100000000000000 : ℝ)^7 := by
    have hnat : (898123411 : ℕ)^9*100000000000000^7 ≤ 10998354928287^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898123411 5000000000 10998354928287 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53049741/200000000 : ℝ), (119510037/156250000 : ℝ), (898123411/5000000000 : ℝ)] ![(18154436723081/100000000000000 : ℝ), (17711802082287/25000000000000 : ℝ), (10998354928287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53049741/200000000 : ℝ)|^9 ≤ (18154436723081/100000000000000 : ℝ)^7
        have hw : |(53049741/200000000 : ℝ)|=(53049741/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119510037/156250000 : ℝ)|^9 ≤ (17711802082287/25000000000000 : ℝ)^7
        have hw : |(119510037/156250000 : ℝ)|=(119510037/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898123411/5000000000 : ℝ)|^9 ≤ (10998354928287/100000000000000 : ℝ)^7
        have hw : |(898123411/5000000000 : ℝ)|=(898123411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311060_s1_s1_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8955854641/10000000000 : ℝ)*x 0 + (2063510903/10000000000 : ℝ)*x 1 + (-36597991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8955854641/10000000000 : ℝ)^9 ≤ (86780736600279/100000000000000 : ℝ)^7 := by
    have hnat : (8955854641 : ℕ)^9*100000000000000^7 ≤ 86780736600279^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8955854641 10000000000 86780736600279 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063510903/10000000000 : ℝ)^9 ≤ (525823657261/4000000000000 : ℝ)^7 := by
    have hnat : (2063510903 : ℕ)^9*4000000000000^7 ≤ 525823657261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063510903 10000000000 525823657261 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36597991/10000000000 : ℝ)^9 ≤ (18417987849/25000000000000 : ℝ)^7 := by
    have hnat : (36597991 : ℕ)^9*25000000000000^7 ≤ 18417987849^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36597991 10000000000 18417987849 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8955854641/10000000000 : ℝ), (2063510903/10000000000 : ℝ), (-36597991/10000000000 : ℝ)] ![(86780736600279/100000000000000 : ℝ), (525823657261/4000000000000 : ℝ), (18417987849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8955854641/10000000000 : ℝ)|^9 ≤ (86780736600279/100000000000000 : ℝ)^7
        have hw : |(8955854641/10000000000 : ℝ)|=(8955854641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063510903/10000000000 : ℝ)|^9 ≤ (525823657261/4000000000000 : ℝ)^7
        have hw : |(2063510903/10000000000 : ℝ)|=(2063510903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36597991/10000000000 : ℝ)|^9 ≤ (18417987849/25000000000000 : ℝ)^7
        have hw : |(-36597991/10000000000 : ℝ)|=(36597991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311060_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((43843/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43843/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2733/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2733/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3979/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3979/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35397/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35397/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2867/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2867/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29459/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29459/50000 : ℝ)*X 1 2) := by
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
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (89829/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (43843/50000 : ℝ) ^ (71/16 : ℝ) ≤ (27907634690255742619/50000000000000000000 : ℝ) := by
    have hpowers : (43843/50000 : ℝ)^71 ≤ (27907634690255742619/50000000000000000000 : ℝ)^16 := by
      have hnat : (43843 : ℕ)^71*50000000000000000000^16 ≤ 27907634690255742619^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43843 50000 27907634690255742619 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43843/50000 : ℝ)) (X := (27907634690255742619/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (77907634690255742619/50000000000000000000 : ℝ) ≤ (11051088930017919/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (77907634690255742619/50000000000000000000 : ℝ)^16 ≤ (11051088930017919/10000000000000000 : ℝ)^71 := by
      have hnat : (77907634690255742619 : ℕ)^16*10000000000000000^71 ≤ 11051088930017919^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77907634690255742619 50000000000000000000 11051088930017919 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11051088930017919/10000000000000000 : ℝ)) (X := (77907634690255742619/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52907634690255742619/25000000000000000000 : ℝ) ≤ (2960123119283207/2500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (52907634690255742619/25000000000000000000 : ℝ)^16 ≤ (2960123119283207/2500000000000000 : ℝ)^71 := by
      have hnat : (52907634690255742619 : ℕ)^16*2500000000000000^71 ≤ 2960123119283207^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52907634690255742619 25000000000000000000 2960123119283207 2500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2960123119283207/2500000000000000 : ℝ)) (X := (52907634690255742619/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1051088930017919/8768600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(789403547114909/8768600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (43843/50000 : ℝ)) (alpha := (1051088930017919/8768600000000000 : ℝ)) (beta := (789403547114909/8768600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (43843/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1051088930017919/8768600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(789403547114909/8768600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2733/3125 : ℝ) ^ (71/16 : ℝ) ≤ (13792131940020796381/25000000000000000000 : ℝ) := by
    have hpowers : (2733/3125 : ℝ)^71 ≤ (13792131940020796381/25000000000000000000 : ℝ)^16 := by
      have hnat : (2733 : ℕ)^71*25000000000000000000^16 ≤ 13792131940020796381^16*3125^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2733 3125 13792131940020796381 25000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2733/3125 : ℝ)) (X := (13792131940020796381/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (38792131940020796381/25000000000000000000 : ℝ) ≤ (11040735437868071/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (38792131940020796381/25000000000000000000 : ℝ)^16 ≤ (11040735437868071/10000000000000000 : ℝ)^71 := by
      have hnat : (38792131940020796381 : ℕ)^16*10000000000000000^71 ≤ 11040735437868071^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38792131940020796381 25000000000000000000 11040735437868071 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11040735437868071/10000000000000000 : ℝ)) (X := (38792131940020796381/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (26292131940020796381/12500000000000000000 : ℝ) ≤ (11824145235145017/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (26292131940020796381/12500000000000000000 : ℝ)^16 ≤ (11824145235145017/10000000000000000 : ℝ)^71 := by
      have hnat : (26292131940020796381 : ℕ)^16*10000000000000000^71 ≤ 11824145235145017^71*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26292131940020796381 12500000000000000000 11824145235145017 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11824145235145017/10000000000000000 : ℝ)) (X := (26292131940020796381/12500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1040735437868071/8745600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(391704898638473/4372800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (2733/3125 : ℝ)) (alpha := (1040735437868071/8745600000000000 : ℝ)) (beta := (391704898638473/4372800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2733/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1040735437868071/8745600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(391704898638473/4372800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3979/5000 : ℝ) ^ (71/16 : ℝ) ≤ (36292548069251645481/100000000000000000000 : ℝ) := by
    have hpowers : (3979/5000 : ℝ)^71 ≤ (36292548069251645481/100000000000000000000 : ℝ)^16 := by
      have hnat : (3979 : ℕ)^71*100000000000000000000^16 ≤ 36292548069251645481^16*5000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3979 5000 36292548069251645481 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3979/5000 : ℝ)) (X := (36292548069251645481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (136292548069251645481/100000000000000000000 : ℝ) ≤ (5361342825785283/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (136292548069251645481/100000000000000000000 : ℝ)^16 ≤ (5361342825785283/5000000000000000 : ℝ)^71 := by
      have hnat : (136292548069251645481 : ℕ)^16*5000000000000000^71 ≤ 5361342825785283^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136292548069251645481 100000000000000000000 5361342825785283 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5361342825785283/5000000000000000 : ℝ)) (X := (136292548069251645481/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (86292548069251645481/50000000000000000000 : ℝ) ≤ (11308609089371711/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (86292548069251645481/50000000000000000000 : ℝ)^16 ≤ (11308609089371711/10000000000000000 : ℝ)^71 := by
      have hnat : (86292548069251645481 : ℕ)^16*10000000000000000^71 ≤ 11308609089371711^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86292548069251645481 50000000000000000000 11308609089371711 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11308609089371711/10000000000000000 : ℝ)) (X := (86292548069251645481/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(361342825785283/3979000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(117184687560229/1591600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (3979/5000 : ℝ)) (alpha := (361342825785283/3979000000000000 : ℝ)) (beta := (117184687560229/1591600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3979/5000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(361342825785283/3979000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(117184687560229/1591600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-417962523/2500000000 : ℝ)*X 0 0+(4471605397/10000000000 : ℝ)*X 0 1+(-3115870519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2256728227/5000000000 : ℝ)*X 1 0+(-426900887/2500000000 : ℝ)*X 1 1+(-246756397/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-971473467/5000000000 : ℝ)*X 0 0+(2527211739/10000000000 : ℝ)*X 0 1+(-3821246611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3002304897/10000000000 : ℝ)*X 1 0+(-1399839453/10000000000 : ℝ)*X 1 1+(-3819364109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3173166777/10000000000 : ℝ)*X 2 0+(7458213629/10000000000 : ℝ)*X 2 1+(738594337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4805648893/10000000000 : ℝ)*X 0 0+(1702525273/2500000000 : ℝ)*X 0 1+(-28481/2000000000 : ℝ)*X 0 2+(4805648893/10000000000 : ℝ)*X 1 0+(1702525273/2500000000 : ℝ)*X 1 1+(-28481/2000000000 : ℝ)*X 1 2+(4805648893/10000000000 : ℝ)*X 2 0+(1702525273/2500000000 : ℝ)*X 2 1+(-28481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1432498027/10000000000 : ℝ)*X 0 0+(2655076159/10000000000 : ℝ)*X 0 1+(-1969717959/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2109487261/10000000000 : ℝ)*X 1 0+(-101811303/500000000 : ℝ)*X 1 1+(-984373333/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1287490971/2000000000 : ℝ)*X 2 0+(4329988609/10000000000 : ℝ)*X 2 1+(311285907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8445775637/10000000000 : ℝ)*X 0 0+(2806384639/10000000000 : ℝ)*X 0 1+(-408727/2000000000 : ℝ)*X 0 2+(8445775637/10000000000 : ℝ)*X 1 0+(2806384639/10000000000 : ℝ)*X 1 1+(-408727/2000000000 : ℝ)*X 1 2+(8445775637/10000000000 : ℝ)*X 2 0+(2806384639/10000000000 : ℝ)*X 2 1+(-408727/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-469855951/5000000000 : ℝ)*X 0 0+(1213798211/2000000000 : ℝ)*X 0 1+(-1287336589/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6252532699/10000000000 : ℝ)*X 1 0+(-1116176829/10000000000 : ℝ)*X 1 1+(-4842171199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((53049741/200000000 : ℝ)*X 2 0+(119510037/156250000 : ℝ)*X 2 1+(898123411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8955854641/10000000000 : ℝ)*X 0 0+(2063510903/10000000000 : ℝ)*X 0 1+(-36597991/10000000000 : ℝ)*X 0 2+(8955854641/10000000000 : ℝ)*X 1 0+(2063510903/10000000000 : ℝ)*X 1 1+(-36597991/10000000000 : ℝ)*X 1 2+(8955854641/10000000000 : ℝ)*X 2 0+(2063510903/10000000000 : ℝ)*X 2 1+(-36597991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((35397/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35397/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4670429075510081870856745644413/635700526268000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11976387243/200000000000 : ℝ)*(base5) + (811135142777/1000000000000 : ℝ)*(base7) + (788467/1000000000000 : ℝ)*(base59) + (1212647625319/500000000000 : ℝ)*(major_s1_0) + (1212647625319/500000000000 : ℝ)*(major_s1_1) + (1212647625319/500000000000 : ℝ)*(major_s1_2) + (6811461/1000000000000 : ℝ)*(sp_s1_0) + (1567251/1000000000000 : ℝ)*(sp_s1_1) + (2889076697193/1000000000000 : ℝ)*(sp_s1_7) + (577824222033/200000000000 : ℝ)*(sp_s1_8) + (2949006408119/1000000000000 : ℝ)*(sp_s1_9) + (556740098839/250000000000 : ℝ)*(sp_s1_13) + (163853/4000000000 : ℝ)*(sp_s1_14) + (1794489/1000000000000 : ℝ)*(sp_s1_15) + (1475707188793/1000000000000 : ℝ)*(f.failure) + (577824894381/200000000000 : ℝ)*(f.sum) + (26839024791580710889/86996856000000000000000000000000 : ℝ)*base62 + (35334284076731/795800000000000000000000000 : ℝ)*base64 + (811545100361953/2186400000000000000000000000 : ℝ)*base66 + (965870448748923/1989500000000000000000000000 : ℝ)*base68 + (636967450847271523/6978051880000000000000000000000 : ℝ)*base70 + (1462604772228001/4384300000000000000000000000 : ℝ)*base73 + (1189427440781231/4372800000000000000000000000 : ℝ)*base74 + (471785146542129/4384300000000000000000000000 : ℝ)*base76 + (427560153107755633/19171667040000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (12009/25000000000000000 : ℝ)*base86 + (12009/25000000000000000 : ℝ)*base88 + (12009/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2867/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2867/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12312282806314291442197720889999/635700526268000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167243296081/200000000000 : ℝ)*(base7) + (86429/1000000000000 : ℝ)*(base50) + (271019/40000000000 : ℝ)*(base53) + (1059766044313/500000000000 : ℝ)*(major_s1_0) + (1059766044313/500000000000 : ℝ)*(major_s1_1) + (2119525313151/1000000000000 : ℝ)*(major_s1_2) + (14712443/1000000000000 : ℝ)*(sp_s1_0) + (8725591/500000000000 : ℝ)*(sp_s1_7) + (100942287/1000000000000 : ℝ)*(sp_s1_8) + (2448581163427/1000000000000 : ℝ)*(sp_s1_14) + (612128096191/250000000000 : ℝ)*(sp_s1_15) + (1224310051263/500000000000 : ℝ)*(sp_s1_16) + (33216189687/15625000000 : ℝ)*(sp_s1_20) + (10339421/250000000000 : ℝ)*(sp_s1_27) + (40301906789/31250000000 : ℝ)*(f.failure) + (1224310051263/500000000000 : ℝ)*(f.sum) + (12169994795084929697/86996856000000000000000000000000 : ℝ)*base63 + (543556590960139/1591600000000000000000000000 : ℝ)*base64 + (1565869653615809/2186400000000000000000000000 : ℝ)*base67 + (257015958953033/3979000000000000000000000000 : ℝ)*base69 + (660447804707366017/13956103760000000000000000000000 : ℝ)*base70 + (274732742863503/4384300000000000000000000000 : ℝ)*base72 + (375201364859023/4372800000000000000000000000 : ℝ)*base75 + (96760011410693/4384300000000000000000000000 : ℝ)*base76 + (303105643145827331/3834333408000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1161/1562500000000000 : ℝ)*base87 + (1161/1562500000000000 : ℝ)*base89 + (1161/1562500000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29459/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29459/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39721823340206727182837338791/3178502631340000000000000000000000 : ℝ) := by norm_num
    linear_combination (592977226257/1000000000000 : ℝ)*(base7) + (4269/1562500000 : ℝ)*(base34) + (79237515051/1000000000000 : ℝ)*(base39) + (6615503/500000000000 : ℝ)*(base43) + (1065722302013/500000000000 : ℝ)*(major_s1_0) + (106571705259/50000000000 : ℝ)*(major_s1_1) + (2131447336187/1000000000000 : ℝ)*(major_s1_2) + (15689947/500000000000 : ℝ)*(sp_s1_0) + (88125241/500000000000 : ℝ)*(sp_s1_9) + (7301451/200000000000 : ℝ)*(sp_s1_20) + (1305410896991/500000000000 : ℝ)*(sp_s1_21) + (2610869137043/1000000000000 : ℝ)*(sp_s1_22) + (522135931111/200000000000 : ℝ)*(sp_s1_23) + (944924507387/500000000000 : ℝ)*(sp_s1_27) + (1296911027933/1000000000000 : ℝ)*(f.failure) + (2610869137043/1000000000000 : ℝ)*(f.sum) + (1633928998090239849/14499476000000000000000000000000 : ℝ)*base63 + (330148190039023/1591600000000000000000000000 : ℝ)*base64 + (21320044565207/72880000000000000000000000 : ℝ)*base66 + (453317321049479/3979000000000000000000000000 : ℝ)*base68 + (3007957454770061937/69780518800000000000000000000000 : ℝ)*base70 + (2600674912308303/4384300000000000000000000000 : ℝ)*base72 + (9971855849869/29152000000000000000000000 : ℝ)*base74 + (2783306776481603/4384300000000000000000000000 : ℝ)*base76 + (6934912050062497997/15976389200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (33171/25000000000000000 : ℝ)*base87 + (33171/25000000000000000 : ℝ)*base89 + (8171/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((43843/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43843/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2733/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2733/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3979/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3979/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35397/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35397/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2867/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2867/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29459/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29459/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311060_s1 p hpa hpb X hX hprev0

#print axioms solution
