-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:24:27.876806+00:00
-- url     : https://prove2.me/submissions/12378115-bc73-43d9-807a-73f78e8617f5

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
theorem collision_support_c302062_s2_s2_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-151426637/1250000000 : ℝ)*x 0 + (2505188431/5000000000 : ℝ)*x 1 + (-625985523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151426637/1250000000 : ℝ)^131 ≤ (6123259897653/100000000000000 : ℝ)^99 := by
    have hnat : (151426637 : ℕ)^131*100000000000000^99 ≤ 6123259897653^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151426637 1250000000 6123259897653 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2505188431/5000000000 : ℝ)^131 ≤ (5009205122469/12500000000000 : ℝ)^99 := by
    have hnat : (2505188431 : ℕ)^131*12500000000000^99 ≤ 5009205122469^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505188431 5000000000 5009205122469 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625985523/1000000000 : ℝ)^131 ≤ (10760619822511/20000000000000 : ℝ)^99 := by
    have hnat : (625985523 : ℕ)^131*20000000000000^99 ≤ 10760619822511^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625985523 1000000000 10760619822511 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-151426637/1250000000 : ℝ), (2505188431/5000000000 : ℝ), (-625985523/1000000000 : ℝ)] ![(6123259897653/100000000000000 : ℝ), (5009205122469/12500000000000 : ℝ), (10760619822511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-151426637/1250000000 : ℝ)|^131 ≤ (6123259897653/100000000000000 : ℝ)^99
        have hw : |(-151426637/1250000000 : ℝ)|=(151426637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2505188431/5000000000 : ℝ)|^131 ≤ (5009205122469/12500000000000 : ℝ)^99
        have hw : |(2505188431/5000000000 : ℝ)|=(2505188431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-625985523/1000000000 : ℝ)|^131 ≤ (10760619822511/20000000000000 : ℝ)^99
        have hw : |(-625985523/1000000000 : ℝ)|=(625985523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1255257067/2500000000 : ℝ)*x 0 + (-1207061011/10000000000 : ℝ)*x 1 + (-6252496583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1255257067/2500000000 : ℝ)^131 ≤ (40186407600319/100000000000000 : ℝ)^99 := by
    have hnat : (1255257067 : ℕ)^131*100000000000000^99 ≤ 40186407600319^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255257067 2500000000 40186407600319 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207061011/10000000000 : ℝ)^131 ≤ (6094168039459/100000000000000 : ℝ)^99 := by
    have hnat : (1207061011 : ℕ)^131*100000000000000^99 ≤ 6094168039459^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207061011 10000000000 6094168039459 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6252496583/10000000000 : ℝ)^131 ≤ (53719424341123/100000000000000 : ℝ)^99 := by
    have hnat : (6252496583 : ℕ)^131*100000000000000^99 ≤ 53719424341123^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6252496583 10000000000 53719424341123 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1255257067/2500000000 : ℝ), (-1207061011/10000000000 : ℝ), (-6252496583/10000000000 : ℝ)] ![(40186407600319/100000000000000 : ℝ), (6094168039459/100000000000000 : ℝ), (53719424341123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1255257067/2500000000 : ℝ)|^131 ≤ (40186407600319/100000000000000 : ℝ)^99
        have hw : |(1255257067/2500000000 : ℝ)|=(1255257067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1207061011/10000000000 : ℝ)|^131 ≤ (6094168039459/100000000000000 : ℝ)^99
        have hw : |(-1207061011/10000000000 : ℝ)|=(1207061011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6252496583/10000000000 : ℝ)|^131 ≤ (53719424341123/100000000000000 : ℝ)^99
        have hw : |(-6252496583/10000000000 : ℝ)|=(6252496583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (540744979/1000000000 : ℝ)*x 0 + (27575647/50000000 : ℝ)*x 1 + (888770851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540744979/1000000000 : ℝ)^131 ≤ (22164454335473/50000000000000 : ℝ)^99 := by
    have hnat : (540744979 : ℕ)^131*50000000000000^99 ≤ 22164454335473^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540744979 1000000000 22164454335473 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27575647/50000000 : ℝ)^131 ≤ (45500708297653/100000000000000 : ℝ)^99 := by
    have hnat : (27575647 : ℕ)^131*100000000000000^99 ≤ 45500708297653^99*50000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27575647 50000000 45500708297653 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888770851/5000000000 : ℝ)^131 ≤ (10170383018451/100000000000000 : ℝ)^99 := by
    have hnat : (888770851 : ℕ)^131*100000000000000^99 ≤ 10170383018451^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888770851 5000000000 10170383018451 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540744979/1000000000 : ℝ), (27575647/50000000 : ℝ), (888770851/5000000000 : ℝ)] ![(22164454335473/50000000000000 : ℝ), (45500708297653/100000000000000 : ℝ), (10170383018451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540744979/1000000000 : ℝ)|^131 ≤ (22164454335473/50000000000000 : ℝ)^99
        have hw : |(540744979/1000000000 : ℝ)|=(540744979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27575647/50000000 : ℝ)|^131 ≤ (45500708297653/100000000000000 : ℝ)^99
        have hw : |(27575647/50000000 : ℝ)|=(27575647/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888770851/5000000000 : ℝ)|^131 ≤ (10170383018451/100000000000000 : ℝ)^99
        have hw : |(888770851/5000000000 : ℝ)|=(888770851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-9985607/62500000 : ℝ)*x 0 + (2353259733/10000000000 : ℝ)*x 1 + (-8161345321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9985607/62500000 : ℝ)^131 ≤ (4415787014709/50000000000000 : ℝ)^99 := by
    have hnat : (9985607 : ℕ)^131*50000000000000^99 ≤ 4415787014709^99*62500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9985607 62500000 4415787014709 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353259733/10000000000 : ℝ)^131 ≤ (7371285938439/50000000000000 : ℝ)^99 := by
    have hnat : (2353259733 : ℕ)^131*50000000000000^99 ≤ 7371285938439^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353259733 10000000000 7371285938439 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8161345321/10000000000 : ℝ)^131 ≤ (38212927038337/50000000000000 : ℝ)^99 := by
    have hnat : (8161345321 : ℕ)^131*50000000000000^99 ≤ 38212927038337^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8161345321 10000000000 38212927038337 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9985607/62500000 : ℝ), (2353259733/10000000000 : ℝ), (-8161345321/10000000000 : ℝ)] ![(4415787014709/50000000000000 : ℝ), (7371285938439/50000000000000 : ℝ), (38212927038337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9985607/62500000 : ℝ)|^131 ≤ (4415787014709/50000000000000 : ℝ)^99
        have hw : |(-9985607/62500000 : ℝ)|=(9985607/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2353259733/10000000000 : ℝ)|^131 ≤ (7371285938439/50000000000000 : ℝ)^99
        have hw : |(2353259733/10000000000 : ℝ)|=(2353259733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8161345321/10000000000 : ℝ)|^131 ≤ (38212927038337/50000000000000 : ℝ)^99
        have hw : |(-8161345321/10000000000 : ℝ)|=(8161345321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2753837273/10000000000 : ℝ)*x 0 + (-1122738841/10000000000 : ℝ)*x 1 + (-1630421041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753837273/10000000000 : ℝ)^131 ≤ (18151320317153/100000000000000 : ℝ)^99 := by
    have hnat : (2753837273 : ℕ)^131*100000000000000^99 ≤ 18151320317153^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753837273 10000000000 18151320317153 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122738841/10000000000 : ℝ)^131 ≤ (5537301108651/100000000000000 : ℝ)^99 := by
    have hnat : (1122738841 : ℕ)^131*100000000000000^99 ≤ 5537301108651^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122738841 10000000000 5537301108651 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1630421041/2000000000 : ℝ)^131 ≤ (3052455142773/4000000000000 : ℝ)^99 := by
    have hnat : (1630421041 : ℕ)^131*4000000000000^99 ≤ 3052455142773^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630421041 2000000000 3052455142773 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753837273/10000000000 : ℝ), (-1122738841/10000000000 : ℝ), (-1630421041/2000000000 : ℝ)] ![(18151320317153/100000000000000 : ℝ), (5537301108651/100000000000000 : ℝ), (3052455142773/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753837273/10000000000 : ℝ)|^131 ≤ (18151320317153/100000000000000 : ℝ)^99
        have hw : |(2753837273/10000000000 : ℝ)|=(2753837273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122738841/10000000000 : ℝ)|^131 ≤ (5537301108651/100000000000000 : ℝ)^99
        have hw : |(-1122738841/10000000000 : ℝ)|=(1122738841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1630421041/2000000000 : ℝ)|^131 ≤ (3052455142773/4000000000000 : ℝ)^99
        have hw : |(-1630421041/2000000000 : ℝ)|=(1630421041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (809761243/2500000000 : ℝ)*x 0 + (3658984607/5000000000 : ℝ)*x 1 + (1930802341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (809761243/2500000000 : ℝ)^131 ≤ (11249621863703/50000000000000 : ℝ)^99 := by
    have hnat : (809761243 : ℕ)^131*50000000000000^99 ≤ 11249621863703^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809761243 2500000000 11249621863703 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3658984607/5000000000 : ℝ)^131 ≤ (6615417071251/10000000000000 : ℝ)^99 := by
    have hnat : (3658984607 : ℕ)^131*10000000000000^99 ≤ 6615417071251^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3658984607 5000000000 6615417071251 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930802341/10000000000 : ℝ)^131 ≤ (1134658554657/10000000000000 : ℝ)^99 := by
    have hnat : (1930802341 : ℕ)^131*10000000000000^99 ≤ 1134658554657^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930802341 10000000000 1134658554657 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(809761243/2500000000 : ℝ), (3658984607/5000000000 : ℝ), (1930802341/10000000000 : ℝ)] ![(11249621863703/50000000000000 : ℝ), (6615417071251/10000000000000 : ℝ), (1134658554657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(809761243/2500000000 : ℝ)|^131 ≤ (11249621863703/50000000000000 : ℝ)^99
        have hw : |(809761243/2500000000 : ℝ)|=(809761243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3658984607/5000000000 : ℝ)|^131 ≤ (6615417071251/10000000000000 : ℝ)^99
        have hw : |(3658984607/5000000000 : ℝ)|=(3658984607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1930802341/10000000000 : ℝ)|^131 ≤ (1134658554657/10000000000000 : ℝ)^99
        have hw : |(1930802341/10000000000 : ℝ)|=(1930802341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (965830349/2500000000 : ℝ)*x 0 + (7768077869/10000000000 : ℝ)*x 1 + (-18789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965830349/2500000000 : ℝ)^131 ≤ (28408822403853/100000000000000 : ℝ)^99 := by
    have hnat : (965830349 : ℕ)^131*100000000000000^99 ≤ 28408822403853^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965830349 2500000000 28408822403853 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7768077869/10000000000 : ℝ)^131 ≤ (71591155305231/100000000000000 : ℝ)^99 := by
    have hnat : (7768077869 : ℕ)^131*100000000000000^99 ≤ 71591155305231^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7768077869 10000000000 71591155305231 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18789/2000000000 : ℝ)^131 ≤ (5570369/25000000000000 : ℝ)^99 := by
    have hnat : (18789 : ℕ)^131*25000000000000^99 ≤ 5570369^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18789 2000000000 5570369 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(965830349/2500000000 : ℝ), (7768077869/10000000000 : ℝ), (-18789/2000000000 : ℝ)] ![(28408822403853/100000000000000 : ℝ), (71591155305231/100000000000000 : ℝ), (5570369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(965830349/2500000000 : ℝ)|^131 ≤ (28408822403853/100000000000000 : ℝ)^99
        have hw : |(965830349/2500000000 : ℝ)|=(965830349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7768077869/10000000000 : ℝ)|^131 ≤ (71591155305231/100000000000000 : ℝ)^99
        have hw : |(7768077869/10000000000 : ℝ)|=(7768077869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18789/2000000000 : ℝ)|^131 ≤ (5570369/25000000000000 : ℝ)^99
        have hw : |(-18789/2000000000 : ℝ)|=(18789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-110931751/1000000000 : ℝ)*x 0 + (2712330979/10000000000 : ℝ)*x 1 + (-51176819/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110931751/1000000000 : ℝ)^131 ≤ (5449881482497/100000000000000 : ℝ)^99 := by
    have hnat : (110931751 : ℕ)^131*100000000000000^99 ≤ 5449881482497^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110931751 1000000000 5449881482497 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712330979/10000000000 : ℝ)^131 ≤ (17790195623543/100000000000000 : ℝ)^99 := by
    have hnat : (2712330979 : ℕ)^131*100000000000000^99 ≤ 17790195623543^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712330979 10000000000 17790195623543 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51176819/62500000 : ℝ)^131 ≤ (76759922885203/100000000000000 : ℝ)^99 := by
    have hnat : (51176819 : ℕ)^131*100000000000000^99 ≤ 76759922885203^99*62500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51176819 62500000 76759922885203 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110931751/1000000000 : ℝ), (2712330979/10000000000 : ℝ), (-51176819/62500000 : ℝ)] ![(5449881482497/100000000000000 : ℝ), (17790195623543/100000000000000 : ℝ), (76759922885203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110931751/1000000000 : ℝ)|^131 ≤ (5449881482497/100000000000000 : ℝ)^99
        have hw : |(-110931751/1000000000 : ℝ)|=(110931751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712330979/10000000000 : ℝ)|^131 ≤ (17790195623543/100000000000000 : ℝ)^99
        have hw : |(2712330979/10000000000 : ℝ)|=(2712330979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51176819/62500000 : ℝ)|^131 ≤ (76759922885203/100000000000000 : ℝ)^99
        have hw : |(-51176819/62500000 : ℝ)|=(51176819/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (466800103/2000000000 : ℝ)*x 0 + (-794767789/5000000000 : ℝ)*x 1 + (-1635804027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466800103/2000000000 : ℝ)^131 ≤ (7291565024689/50000000000000 : ℝ)^99 := by
    have hnat : (466800103 : ℕ)^131*50000000000000^99 ≤ 7291565024689^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466800103 2000000000 7291565024689 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794767789/5000000000 : ℝ)^131 ≤ (8771926443397/100000000000000 : ℝ)^99 := by
    have hnat : (794767789 : ℕ)^131*100000000000000^99 ≤ 8771926443397^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794767789 5000000000 8771926443397 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1635804027/2000000000 : ℝ)^131 ≤ (76644943496739/100000000000000 : ℝ)^99 := by
    have hnat : (1635804027 : ℕ)^131*100000000000000^99 ≤ 76644943496739^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635804027 2000000000 76644943496739 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(466800103/2000000000 : ℝ), (-794767789/5000000000 : ℝ), (-1635804027/2000000000 : ℝ)] ![(7291565024689/50000000000000 : ℝ), (8771926443397/100000000000000 : ℝ), (76644943496739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(466800103/2000000000 : ℝ)|^131 ≤ (7291565024689/50000000000000 : ℝ)^99
        have hw : |(466800103/2000000000 : ℝ)|=(466800103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-794767789/5000000000 : ℝ)|^131 ≤ (8771926443397/100000000000000 : ℝ)^99
        have hw : |(-794767789/5000000000 : ℝ)|=(794767789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1635804027/2000000000 : ℝ)|^131 ≤ (76644943496739/100000000000000 : ℝ)^99
        have hw : |(-1635804027/2000000000 : ℝ)|=(1635804027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7229207871/10000000000 : ℝ)*x 0 + (1674112327/5000000000 : ℝ)*x 1 + (1937321457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7229207871/10000000000 : ℝ)^131 ≤ (65094497155731/100000000000000 : ℝ)^99 := by
    have hnat : (7229207871 : ℕ)^131*100000000000000^99 ≤ 65094497155731^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7229207871 10000000000 65094497155731 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674112327/5000000000 : ℝ)^131 ≤ (23508196154607/100000000000000 : ℝ)^99 := by
    have hnat : (1674112327 : ℕ)^131*100000000000000^99 ≤ 23508196154607^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674112327 5000000000 23508196154607 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1937321457/10000000000 : ℝ)^131 ≤ (11397306677069/100000000000000 : ℝ)^99 := by
    have hnat : (1937321457 : ℕ)^131*100000000000000^99 ≤ 11397306677069^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937321457 10000000000 11397306677069 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7229207871/10000000000 : ℝ), (1674112327/5000000000 : ℝ), (1937321457/10000000000 : ℝ)] ![(65094497155731/100000000000000 : ℝ), (23508196154607/100000000000000 : ℝ), (11397306677069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7229207871/10000000000 : ℝ)|^131 ≤ (65094497155731/100000000000000 : ℝ)^99
        have hw : |(7229207871/10000000000 : ℝ)|=(7229207871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1674112327/5000000000 : ℝ)|^131 ≤ (23508196154607/100000000000000 : ℝ)^99
        have hw : |(1674112327/5000000000 : ℝ)|=(1674112327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1937321457/10000000000 : ℝ)|^131 ≤ (11397306677069/100000000000000 : ℝ)^99
        have hw : |(1937321457/10000000000 : ℝ)|=(1937321457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7887106613/10000000000 : ℝ)*x 0 + (742562883/2000000000 : ℝ)*x 1 + (-13447/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7887106613/10000000000 : ℝ)^131 ≤ (36523146733863/50000000000000 : ℝ)^99 := by
    have hnat : (7887106613 : ℕ)^131*50000000000000^99 ≤ 36523146733863^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7887106613 10000000000 36523146733863 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742562883/2000000000 : ℝ)^131 ≤ (5390727964443/20000000000000 : ℝ)^99 := by
    have hnat : (742562883 : ℕ)^131*20000000000000^99 ≤ 5390727964443^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742562883 2000000000 5390727964443 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13447/625000000 : ℝ)^131 ≤ (16675461/25000000000000 : ℝ)^99 := by
    have hnat : (13447 : ℕ)^131*25000000000000^99 ≤ 16675461^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13447 625000000 16675461 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7887106613/10000000000 : ℝ), (742562883/2000000000 : ℝ), (-13447/625000000 : ℝ)] ![(36523146733863/50000000000000 : ℝ), (5390727964443/20000000000000 : ℝ), (16675461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7887106613/10000000000 : ℝ)|^131 ≤ (36523146733863/50000000000000 : ℝ)^99
        have hw : |(7887106613/10000000000 : ℝ)|=(7887106613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742562883/2000000000 : ℝ)|^131 ≤ (5390727964443/20000000000000 : ℝ)^99
        have hw : |(742562883/2000000000 : ℝ)|=(742562883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13447/625000000 : ℝ)|^131 ≤ (16675461/25000000000000 : ℝ)^99
        have hw : |(-13447/625000000 : ℝ)|=(13447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-444853181/10000000000 : ℝ)*x 0 + (3414334529/5000000000 : ℝ)*x 1 + (-962788829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444853181/10000000000 : ℝ)^131 ≤ (406646138543/25000000000000 : ℝ)^99 := by
    have hnat : (444853181 : ℕ)^131*25000000000000^99 ≤ 406646138543^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444853181 10000000000 406646138543 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3414334529/5000000000 : ℝ)^131 ≤ (60365406206743/100000000000000 : ℝ)^99 := by
    have hnat : (3414334529 : ℕ)^131*100000000000000^99 ≤ 60365406206743^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3414334529 5000000000 60365406206743 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (962788829/2000000000 : ℝ)^131 ≤ (19004004609067/50000000000000 : ℝ)^99 := by
    have hnat : (962788829 : ℕ)^131*50000000000000^99 ≤ 19004004609067^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962788829 2000000000 19004004609067 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444853181/10000000000 : ℝ), (3414334529/5000000000 : ℝ), (-962788829/2000000000 : ℝ)] ![(406646138543/25000000000000 : ℝ), (60365406206743/100000000000000 : ℝ), (19004004609067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444853181/10000000000 : ℝ)|^131 ≤ (406646138543/25000000000000 : ℝ)^99
        have hw : |(-444853181/10000000000 : ℝ)|=(444853181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3414334529/5000000000 : ℝ)|^131 ≤ (60365406206743/100000000000000 : ℝ)^99
        have hw : |(3414334529/5000000000 : ℝ)|=(3414334529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-962788829/2000000000 : ℝ)|^131 ≤ (19004004609067/50000000000000 : ℝ)^99
        have hw : |(-962788829/2000000000 : ℝ)|=(962788829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7021141783/10000000000 : ℝ)*x 0 + (-619352069/10000000000 : ℝ)*x 1 + (-2254375753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7021141783/10000000000 : ℝ)^131 ≤ (62627022033643/100000000000000 : ℝ)^99 := by
    have hnat : (7021141783 : ℕ)^131*100000000000000^99 ≤ 62627022033643^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7021141783 10000000000 62627022033643 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (619352069/10000000000 : ℝ)^131 ≤ (315037887939/12500000000000 : ℝ)^99 := by
    have hnat : (619352069 : ℕ)^131*12500000000000^99 ≤ 315037887939^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619352069 10000000000 315037887939 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254375753/5000000000 : ℝ)^131 ≤ (2178292178109/6250000000000 : ℝ)^99 := by
    have hnat : (2254375753 : ℕ)^131*6250000000000^99 ≤ 2178292178109^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254375753 5000000000 2178292178109 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7021141783/10000000000 : ℝ), (-619352069/10000000000 : ℝ), (-2254375753/5000000000 : ℝ)] ![(62627022033643/100000000000000 : ℝ), (315037887939/12500000000000 : ℝ), (2178292178109/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7021141783/10000000000 : ℝ)|^131 ≤ (62627022033643/100000000000000 : ℝ)^99
        have hw : |(7021141783/10000000000 : ℝ)|=(7021141783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-619352069/10000000000 : ℝ)|^131 ≤ (315037887939/12500000000000 : ℝ)^99
        have hw : |(-619352069/10000000000 : ℝ)|=(619352069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2254375753/5000000000 : ℝ)|^131 ≤ (2178292178109/6250000000000 : ℝ)^99
        have hw : |(-2254375753/5000000000 : ℝ)|=(2254375753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (587039293/2000000000 : ℝ)*x 0 + (1471889617/2000000000 : ℝ)*x 1 + (2214021481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (587039293/2000000000 : ℝ)^131 ≤ (19749690912799/100000000000000 : ℝ)^99 := by
    have hnat : (587039293 : ℕ)^131*100000000000000^99 ≤ 19749690912799^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587039293 2000000000 19749690912799 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1471889617/2000000000 : ℝ)^131 ≤ (66650793710871/100000000000000 : ℝ)^99 := by
    have hnat : (1471889617 : ℕ)^131*100000000000000^99 ≤ 66650793710871^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471889617 2000000000 66650793710871 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214021481/10000000000 : ℝ)^131 ≤ (2719903071977/20000000000000 : ℝ)^99 := by
    have hnat : (2214021481 : ℕ)^131*20000000000000^99 ≤ 2719903071977^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214021481 10000000000 2719903071977 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(587039293/2000000000 : ℝ), (1471889617/2000000000 : ℝ), (2214021481/10000000000 : ℝ)] ![(19749690912799/100000000000000 : ℝ), (66650793710871/100000000000000 : ℝ), (2719903071977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(587039293/2000000000 : ℝ)|^131 ≤ (19749690912799/100000000000000 : ℝ)^99
        have hw : |(587039293/2000000000 : ℝ)|=(587039293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1471889617/2000000000 : ℝ)|^131 ≤ (66650793710871/100000000000000 : ℝ)^99
        have hw : |(1471889617/2000000000 : ℝ)|=(1471889617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2214021481/10000000000 : ℝ)|^131 ≤ (2719903071977/20000000000000 : ℝ)^99
        have hw : |(2214021481/10000000000 : ℝ)|=(2214021481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s2_s2_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4169499939/5000000000 : ℝ)*x 0 + (618636869/2000000000 : ℝ)*x 1 + (-90113251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169499939/5000000000 : ℝ)^131 ≤ (78634920476603/100000000000000 : ℝ)^99 := by
    have hnat : (4169499939 : ℕ)^131*100000000000000^99 ≤ 78634920476603^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169499939 5000000000 78634920476603 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618636869/2000000000 : ℝ)^131 ≤ (5292105532957/25000000000000 : ℝ)^99 := by
    have hnat : (618636869 : ℕ)^131*25000000000000^99 ≤ 5292105532957^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618636869 2000000000 5292105532957 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90113251/10000000000 : ℝ)^131 ≤ (98328688967/50000000000000 : ℝ)^99 := by
    have hnat : (90113251 : ℕ)^131*50000000000000^99 ≤ 98328688967^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90113251 10000000000 98328688967 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169499939/5000000000 : ℝ), (618636869/2000000000 : ℝ), (-90113251/10000000000 : ℝ)] ![(78634920476603/100000000000000 : ℝ), (5292105532957/25000000000000 : ℝ), (98328688967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169499939/5000000000 : ℝ)|^131 ≤ (78634920476603/100000000000000 : ℝ)^99
        have hw : |(4169499939/5000000000 : ℝ)|=(4169499939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618636869/2000000000 : ℝ)|^131 ≤ (5292105532957/25000000000000 : ℝ)^99
        have hw : |(618636869/2000000000 : ℝ)|=(618636869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90113251/10000000000 : ℝ)|^131 ≤ (98328688967/50000000000000 : ℝ)^99
        have hw : |(-90113251/10000000000 : ℝ)|=(90113251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302062_s2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((44753/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44753/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22243/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22243/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-14821/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-14821/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4011/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4011/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80097/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80097/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31839/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31839/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
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
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (44753/50000 : ℝ) ^ (65/16 : ℝ) ≤ (6373813555997240297/10000000000000000000 : ℝ) := by
    have hpowers : (44753/50000 : ℝ)^65 ≤ (6373813555997240297/10000000000000000000 : ℝ)^16 := by
      have hnat : (44753 : ℕ)^65*10000000000000000000^16 ≤ 6373813555997240297^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44753 50000 6373813555997240297 10000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44753/50000 : ℝ)) (X := (6373813555997240297/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (16373813555997240297/10000000000000000000 : ℝ) ≤ (11290516427704067/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (16373813555997240297/10000000000000000000 : ℝ)^16 ≤ (11290516427704067/10000000000000000 : ℝ)^65 := by
      have hnat : (16373813555997240297 : ℕ)^16*10000000000000000^65 ≤ 11290516427704067^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16373813555997240297 10000000000000000000 11290516427704067 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11290516427704067/10000000000000000 : ℝ)) (X := (16373813555997240297/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (11373813555997240297/5000000000000000000 : ℝ) ≤ (1530281073662213/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (11373813555997240297/5000000000000000000 : ℝ)^16 ≤ (1530281073662213/1250000000000000 : ℝ)^65 := by
      have hnat : (11373813555997240297 : ℕ)^16*1250000000000000^65 ≤ 1530281073662213^65*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373813555997240297 5000000000000000000 1530281073662213 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1530281073662213/1250000000000000 : ℝ)) (X := (11373813555997240297/5000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1290516427704067/8950600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(951732161593637/8950600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (44753/50000 : ℝ)) (alpha := (1290516427704067/8950600000000000 : ℝ)) (beta := (951732161593637/8950600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (44753/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1290516427704067/8950600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(951732161593637/8950600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (22243/25000 : ℝ) ^ (65/16 : ℝ) ≤ (62207356625338853471/100000000000000000000 : ℝ) := by
    have hpowers : (22243/25000 : ℝ)^65 ≤ (62207356625338853471/100000000000000000000 : ℝ)^16 := by
      have hnat : (22243 : ℕ)^65*100000000000000000000^16 ≤ 62207356625338853471^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22243 25000 62207356625338853471 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22243/25000 : ℝ)) (X := (62207356625338853471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (162207356625338853471/100000000000000000000 : ℝ) ≤ (11264441737963217/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (162207356625338853471/100000000000000000000 : ℝ)^16 ≤ (11264441737963217/10000000000000000 : ℝ)^65 := by
      have hnat : (162207356625338853471 : ℕ)^16*10000000000000000^65 ≤ 11264441737963217^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        162207356625338853471 100000000000000000000 11264441737963217 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11264441737963217/10000000000000000 : ℝ)) (X := (162207356625338853471/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (112207356625338853471/50000000000000000000 : ℝ) ≤ (12201483426780101/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (112207356625338853471/50000000000000000000 : ℝ)^16 ≤ (12201483426780101/10000000000000000 : ℝ)^65 := by
      have hnat : (112207356625338853471 : ℕ)^16*10000000000000000^65 ≤ 12201483426780101^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112207356625338853471 50000000000000000000 12201483426780101 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12201483426780101/10000000000000000 : ℝ)) (X := (112207356625338853471/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1264441737963217/8897200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(8077945593249/76700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (22243/25000 : ℝ)) (alpha := (1264441737963217/8897200000000000 : ℝ)) (beta := (8077945593249/76700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (22243/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1264441737963217/8897200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(8077945593249/76700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (14821/20000 : ℝ) ^ (65/16 : ℝ) ≤ (14798766584137972179/50000000000000000000 : ℝ) := by
    have hpowers : (14821/20000 : ℝ)^65 ≤ (14798766584137972179/50000000000000000000 : ℝ)^16 := by
      have hnat : (14821 : ℕ)^65*50000000000000000000^16 ≤ 14798766584137972179^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14821 20000 14798766584137972179 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14821/20000 : ℝ)) (X := (14798766584137972179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (64798766584137972179/50000000000000000000 : ℝ) ≤ (10658991586037067/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (64798766584137972179/50000000000000000000 : ℝ)^16 ≤ (10658991586037067/10000000000000000 : ℝ)^65 := by
      have hnat : (64798766584137972179 : ℕ)^16*10000000000000000^65 ≤ 10658991586037067^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64798766584137972179 50000000000000000000 10658991586037067 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10658991586037067/10000000000000000 : ℝ)) (X := (64798766584137972179/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (39798766584137972179/25000000000000000000 : ℝ) ≤ (11212585010063223/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (39798766584137972179/25000000000000000000 : ℝ)^16 ≤ (11212585010063223/10000000000000000 : ℝ)^65 := by
      have hnat : (39798766584137972179 : ℕ)^16*10000000000000000^65 ≤ 11212585010063223^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39798766584137972179 25000000000000000000 11212585010063223 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11212585010063223/10000000000000000 : ℝ)) (X := (39798766584137972179/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(658991586037067/7410500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(138398356006539/1852625000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (14821/20000 : ℝ)) (alpha := (658991586037067/7410500000000000 : ℝ)) (beta := (138398356006539/1852625000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (14821/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(658991586037067/7410500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(138398356006539/1852625000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-151426637/1250000000 : ℝ)*X 0 0+(2505188431/5000000000 : ℝ)*X 0 1+(-625985523/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1255257067/2500000000 : ℝ)*X 1 0+(-1207061011/10000000000 : ℝ)*X 1 1+(-6252496583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((540744979/1000000000 : ℝ)*X 2 0+(27575647/50000000 : ℝ)*X 2 1+(888770851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-9985607/62500000 : ℝ)*X 0 0+(2353259733/10000000000 : ℝ)*X 0 1+(-8161345321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2753837273/10000000000 : ℝ)*X 1 0+(-1122738841/10000000000 : ℝ)*X 1 1+(-1630421041/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((809761243/2500000000 : ℝ)*X 2 0+(3658984607/5000000000 : ℝ)*X 2 1+(1930802341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((965830349/2500000000 : ℝ)*X 0 0+(7768077869/10000000000 : ℝ)*X 0 1+(-18789/2000000000 : ℝ)*X 0 2+(965830349/2500000000 : ℝ)*X 1 0+(7768077869/10000000000 : ℝ)*X 1 1+(-18789/2000000000 : ℝ)*X 1 2+(965830349/2500000000 : ℝ)*X 2 0+(7768077869/10000000000 : ℝ)*X 2 1+(-18789/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-110931751/1000000000 : ℝ)*X 0 0+(2712330979/10000000000 : ℝ)*X 0 1+(-51176819/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((466800103/2000000000 : ℝ)*X 1 0+(-794767789/5000000000 : ℝ)*X 1 1+(-1635804027/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((7229207871/10000000000 : ℝ)*X 2 0+(1674112327/5000000000 : ℝ)*X 2 1+(1937321457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7887106613/10000000000 : ℝ)*X 0 0+(742562883/2000000000 : ℝ)*X 0 1+(-13447/625000000 : ℝ)*X 0 2+(7887106613/10000000000 : ℝ)*X 1 0+(742562883/2000000000 : ℝ)*X 1 1+(-13447/625000000 : ℝ)*X 1 2+(7887106613/10000000000 : ℝ)*X 2 0+(742562883/2000000000 : ℝ)*X 2 1+(-13447/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-444853181/10000000000 : ℝ)*X 0 0+(3414334529/5000000000 : ℝ)*X 0 1+(-962788829/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7021141783/10000000000 : ℝ)*X 1 0+(-619352069/10000000000 : ℝ)*X 1 1+(-2254375753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((587039293/2000000000 : ℝ)*X 2 0+(1471889617/2000000000 : ℝ)*X 2 1+(2214021481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4169499939/5000000000 : ℝ)*X 0 0+(618636869/2000000000 : ℝ)*X 0 1+(-90113251/10000000000 : ℝ)*X 0 2+(4169499939/5000000000 : ℝ)*X 1 0+(618636869/2000000000 : ℝ)*X 1 1+(-90113251/10000000000 : ℝ)*X 1 2+(4169499939/5000000000 : ℝ)*X 2 0+(618636869/2000000000 : ℝ)*X 2 1+(-90113251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((4011/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4011/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17582285303247191897010757803/1222930267718750000000000000000000 : ℝ) := by norm_num
    linear_combination (100316718783/125000000000 : ℝ)*(base7) + (561609/1000000000000 : ℝ)*(base49) + (50723/40000000000 : ℝ)*(base60) + (2106304949099/1000000000000 : ℝ)*(major_s2_0) + (2106304949099/1000000000000 : ℝ)*(major_s2_1) + (2106304949099/1000000000000 : ℝ)*(major_s2_2) + (1977661/200000000000 : ℝ)*(sp_s2_0) + (5770549/1000000000000 : ℝ)*(sp_s2_1) + (2308887030801/1000000000000 : ℝ)*(sp_s2_7) + (2308984295099/1000000000000 : ℝ)*(sp_s2_8) + (2308996599949/1000000000000 : ℝ)*(sp_s2_9) + (2214550207393/1000000000000 : ℝ)*(sp_s2_13) + (99680843/1000000000000 : ℝ)*(sp_s2_14) + (6534301/1000000000000 : ℝ)*(sp_s2_15) + (1412016457129/1000000000000 : ℝ)*(f.failure) + (2308996599949/1000000000000 : ℝ)*(f.sum) + (16902565889281428293/50717462000000000000000000000000 : ℝ)*base62 + (2500725475901797/3705250000000000000000000000 : ℝ)*base65 + (2525657981033/5900000000000000000000000 : ℝ)*base66 + (1301051128519467/7410500000000000000000000000 : ℝ)*base68 + (352965044805983638829/663284213000000000000000000000000 : ℝ)*base71 + (1618788254204017/8950600000000000000000000000 : ℝ)*base72 + (86415210140551/684400000000000000000000000 : ℝ)*base75 + (3518160338264453/8950600000000000000000000000 : ℝ)*base77 + (92362766751522981/528085400000000000000000000000 : ℝ)*base78 + (3293/10000000000000000 : ℝ)*base87 + (3293/10000000000000000 : ℝ)*base89 + (3293/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80097/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80097/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (263314680633652100364152146398621/14753430749759000000000000000000000000 : ℝ) := by norm_num
    linear_combination (401661979887/500000000000 : ℝ)*(base7) + (49977/200000000000 : ℝ)*(base40) + (399497/500000000000 : ℝ)*(base59) + (2076150448791/1000000000000 : ℝ)*(major_s2_0) + (2076150448791/1000000000000 : ℝ)*(major_s2_1) + (2076150448791/1000000000000 : ℝ)*(major_s2_2) + (1045277/1000000000000 : ℝ)*(sp_s2_2) + (3862513/25000000000 : ℝ)*(sp_s2_8) + (283551908569/125000000000 : ℝ)*(sp_s2_14) + (567065688719/250000000000 : ℝ)*(sp_s2_15) + (2268416210119/1000000000000 : ℝ)*(sp_s2_16) + (219508992379/100000000000 : ℝ)*(sp_s2_20) + (1986843/1000000000000 : ℝ)*(sp_s2_21) + (35637373/1000000000000 : ℝ)*(sp_s2_27) + (347950400347/250000000000 : ℝ)*(f.failure) + (567104313849/250000000000 : ℝ)*(f.sum) + (239853928643360225581/659327006000000000000000000000000 : ℝ)*base62 + (1403602873309273/3705250000000000000000000000 : ℝ)*base65 + (62961283869981/76700000000000000000000000 : ℝ)*base66 + (239553320231203/7410500000000000000000000000 : ℝ)*base68 + (486750109492739144039/663284213000000000000000000000000 : ℝ)*base70 + (2209796395661647/8950600000000000000000000000 : ℝ)*base73 + (1280250441521313/8897200000000000000000000000 : ℝ)*base74 + (1530068450731663/8950600000000000000000000000 : ℝ)*base76 + (3033661086544524563/6865110200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1301/2500000000000000 : ℝ)*base86 + (1301/2500000000000000 : ℝ)*base88 + (1301/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31839/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31839/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17179167770935350997991517030927/7376715374879500000000000000000000000 : ℝ) := by norm_num
    linear_combination (70497197253/125000000000 : ℝ)*(base7) + (65153226803/1000000000000 : ℝ)*(base39) + (131303/125000000000 : ℝ)*(base43) + (135579/250000000000 : ℝ)*(base50) + (8120508489/500000000000 : ℝ)*(base59) + (956595920107/500000000000 : ℝ)*(major_s2_0) + (191319078979/100000000000 : ℝ)*(major_s2_1) + (956595920107/500000000000 : ℝ)*(major_s2_2) + (1027637/20000000000 : ℝ)*(sp_s2_9) + (6354303/1000000000000 : ℝ)*(sp_s2_20) + (8587341173/3906250000 : ℝ)*(sp_s2_21) + (2198360390713/1000000000000 : ℝ)*(sp_s2_22) + (1099153979219/500000000000 : ℝ)*(sp_s2_23) + (184652927173/100000000000 : ℝ)*(sp_s2_27) + (160319756001/125000000000 : ℝ)*(f.failure) + (2198360390713/1000000000000 : ℝ)*(f.sum) + (216351125789342829457/329663503000000000000000000000000 : ℝ)*base62 + (185931428206717/3705250000000000000000000000 : ℝ)*base65 + (1138726917053/7670000000000000000000000 : ℝ)*base67 + (4038556555231781/3705250000000000000000000000 : ℝ)*base68 + (91585790268657943803/331642106500000000000000000000000 : ℝ)*base70 + (2877848413411079/4475300000000000000000000000 : ℝ)*base73 + (136682105675637/177944000000000000000000000 : ℝ)*base74 + (229790504985919/4475300000000000000000000000 : ℝ)*base77 + (1305049624783207163/3432555100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (583/1250000000000000 : ℝ)*base86 + (583/1250000000000000 : ℝ)*base88 + (583/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((44753/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44753/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22243/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22243/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-14821/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-14821/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4011/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4011/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80097/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80097/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31839/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31839/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302062_s2 p hpa hpb X hX hprev1

#print axioms solution
