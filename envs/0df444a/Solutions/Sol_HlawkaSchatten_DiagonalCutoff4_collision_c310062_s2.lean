-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:09.182643+00:00
-- url     : https://prove2.me/submissions/c506aef1-fe84-42a5-b8f6-4c08975b23d5

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
theorem collision_support_c310062_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-413304221/2500000000 : ℝ)*x 0 + (2472129351/5000000000 : ℝ)*x 1 + (-2919234259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413304221/2500000000 : ℝ)^71 ≤ (9793431139963/100000000000000 : ℝ)^55 := by
    have hnat : (413304221 : ℕ)^71*100000000000000^55 ≤ 9793431139963^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413304221 2500000000 9793431139963 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2472129351/5000000000 : ℝ)^71 ≤ (40282131313099/100000000000000 : ℝ)^55 := by
    have hnat : (2472129351 : ℕ)^71*100000000000000^55 ≤ 40282131313099^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472129351 5000000000 40282131313099 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2919234259/5000000000 : ℝ)^71 ≤ (12481109383443/25000000000000 : ℝ)^55 := by
    have hnat : (2919234259 : ℕ)^71*25000000000000^55 ≤ 12481109383443^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919234259 5000000000 12481109383443 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413304221/2500000000 : ℝ), (2472129351/5000000000 : ℝ), (-2919234259/5000000000 : ℝ)] ![(9793431139963/100000000000000 : ℝ), (40282131313099/100000000000000 : ℝ), (12481109383443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413304221/2500000000 : ℝ)|^71 ≤ (9793431139963/100000000000000 : ℝ)^55
        have hw : |(-413304221/2500000000 : ℝ)|=(413304221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2472129351/5000000000 : ℝ)|^71 ≤ (40282131313099/100000000000000 : ℝ)^55
        have hw : |(2472129351/5000000000 : ℝ)|=(2472129351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2919234259/5000000000 : ℝ)|^71 ≤ (12481109383443/25000000000000 : ℝ)^55
        have hw : |(-2919234259/5000000000 : ℝ)|=(2919234259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1238371371/2500000000 : ℝ)*x 0 + (-1659821069/10000000000 : ℝ)*x 1 + (-1165018527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1238371371/2500000000 : ℝ)^71 ≤ (2018959953467/5000000000000 : ℝ)^55 := by
    have hnat : (1238371371 : ℕ)^71*5000000000000^55 ≤ 2018959953467^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238371371 2500000000 2018959953467 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1659821069/10000000000 : ℝ)^71 ≤ (9843963777809/100000000000000 : ℝ)^55 := by
    have hnat : (1659821069 : ℕ)^71*100000000000000^55 ≤ 9843963777809^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659821069 10000000000 9843963777809 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1165018527/2000000000 : ℝ)^71 ≤ (24888418567021/50000000000000 : ℝ)^55 := by
    have hnat : (1165018527 : ℕ)^71*50000000000000^55 ≤ 24888418567021^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165018527 2000000000 24888418567021 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1238371371/2500000000 : ℝ), (-1659821069/10000000000 : ℝ), (-1165018527/2000000000 : ℝ)] ![(2018959953467/5000000000000 : ℝ), (9843963777809/100000000000000 : ℝ), (24888418567021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1238371371/2500000000 : ℝ)|^71 ≤ (2018959953467/5000000000000 : ℝ)^55
        have hw : |(1238371371/2500000000 : ℝ)|=(1238371371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1659821069/10000000000 : ℝ)|^71 ≤ (9843963777809/100000000000000 : ℝ)^55
        have hw : |(-1659821069/10000000000 : ℝ)|=(1659821069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1165018527/2000000000 : ℝ)|^71 ≤ (24888418567021/50000000000000 : ℝ)^55
        have hw : |(-1165018527/2000000000 : ℝ)|=(1165018527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5226509607/10000000000 : ℝ)*x 0 + (1309442667/2500000000 : ℝ)*x 1 + (524785471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226509607/10000000000 : ℝ)^71 ≤ (43274991402417/100000000000000 : ℝ)^55 := by
    have hnat : (5226509607 : ℕ)^71*100000000000000^55 ≤ 43274991402417^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226509607 10000000000 43274991402417 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309442667/2500000000 : ℝ)^71 ≤ (8679078820347/20000000000000 : ℝ)^55 := by
    have hnat : (1309442667 : ℕ)^71*20000000000000^55 ≤ 8679078820347^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309442667 2500000000 8679078820347 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524785471/2500000000 : ℝ)^71 ≤ (6664807238807/50000000000000 : ℝ)^55 := by
    have hnat : (524785471 : ℕ)^71*50000000000000^55 ≤ 6664807238807^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524785471 2500000000 6664807238807 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226509607/10000000000 : ℝ), (1309442667/2500000000 : ℝ), (524785471/2500000000 : ℝ)] ![(43274991402417/100000000000000 : ℝ), (8679078820347/20000000000000 : ℝ), (6664807238807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226509607/10000000000 : ℝ)|^71 ≤ (43274991402417/100000000000000 : ℝ)^55
        have hw : |(5226509607/10000000000 : ℝ)|=(5226509607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309442667/2500000000 : ℝ)|^71 ≤ (8679078820347/20000000000000 : ℝ)^55
        have hw : |(1309442667/2500000000 : ℝ)|=(1309442667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524785471/2500000000 : ℝ)|^71 ≤ (6664807238807/50000000000000 : ℝ)^55
        have hw : |(524785471/2500000000 : ℝ)|=(524785471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5562012887/10000000000 : ℝ)*x 0 + (2771224849/5000000000 : ℝ)*x 1 + (-47705377/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5562012887/10000000000 : ℝ)^71 ≤ (2344702060857/5000000000000 : ℝ)^55 := by
    have hnat : (5562012887 : ℕ)^71*5000000000000^55 ≤ 2344702060857^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562012887 10000000000 2344702060857 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771224849/5000000000 : ℝ)^71 ≤ (46681228022743/100000000000000 : ℝ)^55 := by
    have hnat : (2771224849 : ℕ)^71*100000000000000^55 ≤ 46681228022743^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771224849 5000000000 46681228022743 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47705377/400000000 : ℝ)^71 ≤ (6424730738821/100000000000000 : ℝ)^55 := by
    have hnat : (47705377 : ℕ)^71*100000000000000^55 ≤ 6424730738821^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47705377 400000000 6424730738821 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5562012887/10000000000 : ℝ), (2771224849/5000000000 : ℝ), (-47705377/400000000 : ℝ)] ![(2344702060857/5000000000000 : ℝ), (46681228022743/100000000000000 : ℝ), (6424730738821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5562012887/10000000000 : ℝ)|^71 ≤ (2344702060857/5000000000000 : ℝ)^55
        have hw : |(5562012887/10000000000 : ℝ)|=(5562012887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771224849/5000000000 : ℝ)|^71 ≤ (46681228022743/100000000000000 : ℝ)^55
        have hw : |(2771224849/5000000000 : ℝ)|=(2771224849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47705377/400000000 : ℝ)|^71 ≤ (6424730738821/100000000000000 : ℝ)^55
        have hw : |(-47705377/400000000 : ℝ)|=(47705377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1233904583/10000000000 : ℝ)*x 0 + (1089165717/2500000000 : ℝ)*x 1 + (-207857903/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1233904583/10000000000 : ℝ)^71 ≤ (3356580996017/50000000000000 : ℝ)^55 := by
    have hnat : (1233904583 : ℕ)^71*50000000000000^55 ≤ 3356580996017^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233904583 10000000000 3356580996017 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089165717/2500000000 : ℝ)^71 ≤ (34212165090467/100000000000000 : ℝ)^55 := by
    have hnat : (1089165717 : ℕ)^71*100000000000000^55 ≤ 34212165090467^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089165717 2500000000 34212165090467 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207857903/312500000 : ℝ)^71 ≤ (3692167056587/6250000000000 : ℝ)^55 := by
    have hnat : (207857903 : ℕ)^71*6250000000000^55 ≤ 3692167056587^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207857903 312500000 3692167056587 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1233904583/10000000000 : ℝ), (1089165717/2500000000 : ℝ), (-207857903/312500000 : ℝ)] ![(3356580996017/50000000000000 : ℝ), (34212165090467/100000000000000 : ℝ), (3692167056587/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1233904583/10000000000 : ℝ)|^71 ≤ (3356580996017/50000000000000 : ℝ)^55
        have hw : |(-1233904583/10000000000 : ℝ)|=(1233904583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089165717/2500000000 : ℝ)|^71 ≤ (34212165090467/100000000000000 : ℝ)^55
        have hw : |(1089165717/2500000000 : ℝ)|=(1089165717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207857903/312500000 : ℝ)|^71 ≤ (3692167056587/6250000000000 : ℝ)^55
        have hw : |(-207857903/312500000 : ℝ)|=(207857903/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2330112599/5000000000 : ℝ)*x 0 + (-765707561/10000000000 : ℝ)*x 1 + (-6649636859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2330112599/5000000000 : ℝ)^71 ≤ (7464031323231/20000000000000 : ℝ)^55 := by
    have hnat : (2330112599 : ℕ)^71*20000000000000^55 ≤ 7464031323231^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2330112599 5000000000 7464031323231 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765707561/10000000000 : ℝ)^71 ≤ (3625990806591/100000000000000 : ℝ)^55 := by
    have hnat : (765707561 : ℕ)^71*100000000000000^55 ≤ 3625990806591^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765707561 10000000000 3625990806591 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6649636859/10000000000 : ℝ)^71 ≤ (29526926280501/50000000000000 : ℝ)^55 := by
    have hnat : (6649636859 : ℕ)^71*50000000000000^55 ≤ 29526926280501^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6649636859 10000000000 29526926280501 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2330112599/5000000000 : ℝ), (-765707561/10000000000 : ℝ), (-6649636859/10000000000 : ℝ)] ![(7464031323231/20000000000000 : ℝ), (3625990806591/100000000000000 : ℝ), (29526926280501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2330112599/5000000000 : ℝ)|^71 ≤ (7464031323231/20000000000000 : ℝ)^55
        have hw : |(2330112599/5000000000 : ℝ)|=(2330112599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-765707561/10000000000 : ℝ)|^71 ≤ (3625990806591/100000000000000 : ℝ)^55
        have hw : |(-765707561/10000000000 : ℝ)|=(765707561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6649636859/10000000000 : ℝ)|^71 ≤ (29526926280501/50000000000000 : ℝ)^55
        have hw : |(-6649636859/10000000000 : ℝ)|=(6649636859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4730418223/10000000000 : ℝ)*x 0 + (1606660507/2500000000 : ℝ)*x 1 + (524407303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4730418223/10000000000 : ℝ)^71 ≤ (4755923633523/12500000000000 : ℝ)^55 := by
    have hnat : (4730418223 : ℕ)^71*12500000000000^55 ≤ 4755923633523^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730418223 10000000000 4755923633523 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1606660507/2500000000 : ℝ)^71 ≤ (7063744055077/12500000000000 : ℝ)^55 := by
    have hnat : (1606660507 : ℕ)^71*12500000000000^55 ≤ 7063744055077^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606660507 2500000000 7063744055077 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524407303/5000000000 : ℝ)^71 ≤ (5442658479293/100000000000000 : ℝ)^55 := by
    have hnat : (524407303 : ℕ)^71*100000000000000^55 ≤ 5442658479293^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524407303 5000000000 5442658479293 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4730418223/10000000000 : ℝ), (1606660507/2500000000 : ℝ), (524407303/5000000000 : ℝ)] ![(4755923633523/12500000000000 : ℝ), (7063744055077/12500000000000 : ℝ), (5442658479293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4730418223/10000000000 : ℝ)|^71 ≤ (4755923633523/12500000000000 : ℝ)^55
        have hw : |(4730418223/10000000000 : ℝ)|=(4730418223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1606660507/2500000000 : ℝ)|^71 ≤ (7063744055077/12500000000000 : ℝ)^55
        have hw : |(1606660507/2500000000 : ℝ)|=(1606660507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524407303/5000000000 : ℝ)|^71 ≤ (5442658479293/100000000000000 : ℝ)^55
        have hw : |(524407303/5000000000 : ℝ)|=(524407303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (100768603/200000000 : ℝ)*x 0 + (6536623771/10000000000 : ℝ)*x 1 + (-4284753/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100768603/200000000 : ℝ)^71 ≤ (8255059679373/20000000000000 : ℝ)^55 := by
    have hnat : (100768603 : ℕ)^71*20000000000000^55 ≤ 8255059679373^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100768603 200000000 8255059679373 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6536623771/10000000000 : ℝ)^71 ≤ (5776145710161/10000000000000 : ℝ)^55 := by
    have hnat : (6536623771 : ℕ)^71*10000000000000^55 ≤ 5776145710161^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6536623771 10000000000 5776145710161 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4284753/156250000 : ℝ)^71 ≤ (963244490533/100000000000000 : ℝ)^55 := by
    have hnat : (4284753 : ℕ)^71*100000000000000^55 ≤ 963244490533^55*156250000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284753 156250000 963244490533 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100768603/200000000 : ℝ), (6536623771/10000000000 : ℝ), (-4284753/156250000 : ℝ)] ![(8255059679373/20000000000000 : ℝ), (5776145710161/10000000000000 : ℝ), (963244490533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100768603/200000000 : ℝ)|^71 ≤ (8255059679373/20000000000000 : ℝ)^55
        have hw : |(100768603/200000000 : ℝ)|=(100768603/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6536623771/10000000000 : ℝ)|^71 ≤ (5776145710161/10000000000000 : ℝ)^55
        have hw : |(6536623771/10000000000 : ℝ)|=(6536623771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4284753/156250000 : ℝ)|^71 ≤ (963244490533/100000000000000 : ℝ)^55
        have hw : |(-4284753/156250000 : ℝ)|=(4284753/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19041421/250000000 : ℝ)*x 0 + (2333646271/5000000000 : ℝ)*x 1 + (-3322710191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19041421/250000000 : ℝ)^71 ≤ (7202495081/200000000000 : ℝ)^55 := by
    have hnat : (19041421 : ℕ)^71*200000000000^55 ≤ 7202495081^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19041421 250000000 7202495081 200000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2333646271/5000000000 : ℝ)^71 ≤ (4674154275383/12500000000000 : ℝ)^55 := by
    have hnat : (2333646271 : ℕ)^71*12500000000000^55 ≤ 4674154275383^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333646271 5000000000 4674154275383 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3322710191/5000000000 : ℝ)^71 ≤ (59005518238221/100000000000000 : ℝ)^55 := by
    have hnat : (3322710191 : ℕ)^71*100000000000000^55 ≤ 59005518238221^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3322710191 5000000000 59005518238221 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19041421/250000000 : ℝ), (2333646271/5000000000 : ℝ), (-3322710191/5000000000 : ℝ)] ![(7202495081/200000000000 : ℝ), (4674154275383/12500000000000 : ℝ), (59005518238221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19041421/250000000 : ℝ)|^71 ≤ (7202495081/200000000000 : ℝ)^55
        have hw : |(-19041421/250000000 : ℝ)|=(19041421/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2333646271/5000000000 : ℝ)|^71 ≤ (4674154275383/12500000000000 : ℝ)^55
        have hw : |(2333646271/5000000000 : ℝ)|=(2333646271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3322710191/5000000000 : ℝ)|^71 ≤ (59005518238221/100000000000000 : ℝ)^55
        have hw : |(-3322710191/5000000000 : ℝ)|=(3322710191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2186571613/5000000000 : ℝ)*x 0 + (-611449003/5000000000 : ℝ)*x 1 + (-1660901377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186571613/5000000000 : ℝ)^71 ≤ (34379323252103/100000000000000 : ℝ)^55 := by
    have hnat : (2186571613 : ℕ)^71*100000000000000^55 ≤ 34379323252103^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186571613 5000000000 34379323252103 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611449003/5000000000 : ℝ)^71 ≤ (1658990002947/25000000000000 : ℝ)^55 := by
    have hnat : (611449003 : ℕ)^71*25000000000000^55 ≤ 1658990002947^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611449003 5000000000 1658990002947 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1660901377/2500000000 : ℝ)^71 ≤ (29492358359491/50000000000000 : ℝ)^55 := by
    have hnat : (1660901377 : ℕ)^71*50000000000000^55 ≤ 29492358359491^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660901377 2500000000 29492358359491 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186571613/5000000000 : ℝ), (-611449003/5000000000 : ℝ), (-1660901377/2500000000 : ℝ)] ![(34379323252103/100000000000000 : ℝ), (1658990002947/25000000000000 : ℝ), (29492358359491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186571613/5000000000 : ℝ)|^71 ≤ (34379323252103/100000000000000 : ℝ)^55
        have hw : |(2186571613/5000000000 : ℝ)|=(2186571613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-611449003/5000000000 : ℝ)|^71 ≤ (1658990002947/25000000000000 : ℝ)^55
        have hw : |(-611449003/5000000000 : ℝ)|=(611449003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1660901377/2500000000 : ℝ)|^71 ≤ (29492358359491/50000000000000 : ℝ)^55
        have hw : |(-1660901377/2500000000 : ℝ)|=(1660901377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6206271279/10000000000 : ℝ)*x 0 + (2482282493/5000000000 : ℝ)*x 1 + (527422021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6206271279/10000000000 : ℝ)^71 ≤ (54021089413059/100000000000000 : ℝ)^55 := by
    have hnat : (6206271279 : ℕ)^71*100000000000000^55 ≤ 54021089413059^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6206271279 10000000000 54021089413059 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482282493/5000000000 : ℝ)^71 ≤ (40495827357357/100000000000000 : ℝ)^55 := by
    have hnat : (2482282493 : ℕ)^71*100000000000000^55 ≤ 40495827357357^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482282493 5000000000 40495827357357 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527422021/5000000000 : ℝ)^71 ≤ (5483083217413/100000000000000 : ℝ)^55 := by
    have hnat : (527422021 : ℕ)^71*100000000000000^55 ≤ 5483083217413^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527422021 5000000000 5483083217413 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6206271279/10000000000 : ℝ), (2482282493/5000000000 : ℝ), (527422021/5000000000 : ℝ)] ![(54021089413059/100000000000000 : ℝ), (40495827357357/100000000000000 : ℝ), (5483083217413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6206271279/10000000000 : ℝ)|^71 ≤ (54021089413059/100000000000000 : ℝ)^55
        have hw : |(6206271279/10000000000 : ℝ)|=(6206271279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2482282493/5000000000 : ℝ)|^71 ≤ (40495827357357/100000000000000 : ℝ)^55
        have hw : |(2482282493/5000000000 : ℝ)|=(2482282493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527422021/5000000000 : ℝ)|^71 ≤ (5483083217413/100000000000000 : ℝ)^55
        have hw : |(527422021/5000000000 : ℝ)|=(527422021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1750389267/2500000000 : ℝ)*x 0 + (903594683/2000000000 : ℝ)*x 1 + (-287707523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1750389267/2500000000 : ℝ)^71 ≤ (31559517056609/50000000000000 : ℝ)^55 := by
    have hnat : (1750389267 : ℕ)^71*50000000000000^55 ≤ 31559517056609^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750389267 2500000000 31559517056609 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903594683/2000000000 : ℝ)^71 ≤ (17928074674341/50000000000000 : ℝ)^55 := by
    have hnat : (903594683 : ℕ)^71*50000000000000^55 ≤ 17928074674341^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903594683 2000000000 17928074674341 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287707523/10000000000 : ℝ)^71 ≤ (204963304089/20000000000000 : ℝ)^55 := by
    have hnat : (287707523 : ℕ)^71*20000000000000^55 ≤ 204963304089^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287707523 10000000000 204963304089 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1750389267/2500000000 : ℝ), (903594683/2000000000 : ℝ), (-287707523/10000000000 : ℝ)] ![(31559517056609/50000000000000 : ℝ), (17928074674341/50000000000000 : ℝ), (204963304089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1750389267/2500000000 : ℝ)|^71 ≤ (31559517056609/50000000000000 : ℝ)^55
        have hw : |(1750389267/2500000000 : ℝ)|=(1750389267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903594683/2000000000 : ℝ)|^71 ≤ (17928074674341/50000000000000 : ℝ)^55
        have hw : |(903594683/2000000000 : ℝ)|=(903594683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-287707523/10000000000 : ℝ)|^71 ≤ (204963304089/20000000000000 : ℝ)^55
        have hw : |(-287707523/10000000000 : ℝ)|=(287707523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-8785943/200000000 : ℝ)*x 0 + (5690179567/10000000000 : ℝ)*x 1 + (-1167913417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8785943/200000000 : ℝ)^71 ≤ (221225137949/12500000000000 : ℝ)^55 := by
    have hnat : (8785943 : ℕ)^71*12500000000000^55 ≤ 221225137949^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8785943 200000000 221225137949 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690179567/10000000000 : ℝ)^71 ≤ (48293634493297/100000000000000 : ℝ)^55 := by
    have hnat : (5690179567 : ℕ)^71*100000000000000^55 ≤ 48293634493297^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690179567 10000000000 48293634493297 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167913417/2000000000 : ℝ)^71 ≤ (49936564392871/100000000000000 : ℝ)^55 := by
    have hnat : (1167913417 : ℕ)^71*100000000000000^55 ≤ 49936564392871^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167913417 2000000000 49936564392871 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8785943/200000000 : ℝ), (5690179567/10000000000 : ℝ), (-1167913417/2000000000 : ℝ)] ![(221225137949/12500000000000 : ℝ), (48293634493297/100000000000000 : ℝ), (49936564392871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8785943/200000000 : ℝ)|^71 ≤ (221225137949/12500000000000 : ℝ)^55
        have hw : |(-8785943/200000000 : ℝ)|=(8785943/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690179567/10000000000 : ℝ)|^71 ≤ (48293634493297/100000000000000 : ℝ)^55
        have hw : |(5690179567/10000000000 : ℝ)|=(5690179567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1167913417/2000000000 : ℝ)|^71 ≤ (49936564392871/100000000000000 : ℝ)^55
        have hw : |(-1167913417/2000000000 : ℝ)|=(1167913417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1250420871/2000000000 : ℝ)*x 0 + (-499281917/5000000000 : ℝ)*x 1 + (-990236289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1250420871/2000000000 : ℝ)^71 ≤ (13634160418297/25000000000000 : ℝ)^55 := by
    have hnat : (1250420871 : ℕ)^71*25000000000000^55 ≤ 13634160418297^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250420871 2000000000 13634160418297 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499281917/5000000000 : ℝ)^71 ≤ (2554201585883/50000000000000 : ℝ)^55 := by
    have hnat : (499281917 : ℕ)^71*50000000000000^55 ≤ 2554201585883^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499281917 5000000000 2554201585883 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990236289/2000000000 : ℝ)^71 ≤ (20177477572943/50000000000000 : ℝ)^55 := by
    have hnat : (990236289 : ℕ)^71*50000000000000^55 ≤ 20177477572943^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990236289 2000000000 20177477572943 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1250420871/2000000000 : ℝ), (-499281917/5000000000 : ℝ), (-990236289/2000000000 : ℝ)] ![(13634160418297/25000000000000 : ℝ), (2554201585883/50000000000000 : ℝ), (20177477572943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1250420871/2000000000 : ℝ)|^71 ≤ (13634160418297/25000000000000 : ℝ)^55
        have hw : |(1250420871/2000000000 : ℝ)|=(1250420871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499281917/5000000000 : ℝ)|^71 ≤ (2554201585883/50000000000000 : ℝ)^55
        have hw : |(-499281917/5000000000 : ℝ)|=(499281917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-990236289/2000000000 : ℝ)|^71 ≤ (20177477572943/50000000000000 : ℝ)^55
        have hw : |(-990236289/2000000000 : ℝ)|=(990236289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2248061661/5000000000 : ℝ)*x 0 + (5987453761/10000000000 : ℝ)*x 1 + (1016656273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248061661/5000000000 : ℝ)^71 ≤ (17816225452841/50000000000000 : ℝ)^55 := by
    have hnat : (2248061661 : ℕ)^71*50000000000000^55 ≤ 17816225452841^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248061661 5000000000 17816225452841 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5987453761/10000000000 : ℝ)^71 ≤ (51575078237017/100000000000000 : ℝ)^55 := by
    have hnat : (5987453761 : ℕ)^71*100000000000000^55 ≤ 51575078237017^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987453761 10000000000 51575078237017 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016656273/5000000000 : ℝ)^71 ≤ (6396235420663/50000000000000 : ℝ)^55 := by
    have hnat : (1016656273 : ℕ)^71*50000000000000^55 ≤ 6396235420663^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016656273 5000000000 6396235420663 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2248061661/5000000000 : ℝ), (5987453761/10000000000 : ℝ), (1016656273/5000000000 : ℝ)] ![(17816225452841/50000000000000 : ℝ), (51575078237017/100000000000000 : ℝ), (6396235420663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2248061661/5000000000 : ℝ)|^71 ≤ (17816225452841/50000000000000 : ℝ)^55
        have hw : |(2248061661/5000000000 : ℝ)|=(2248061661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5987453761/10000000000 : ℝ)|^71 ≤ (51575078237017/100000000000000 : ℝ)^55
        have hw : |(5987453761/10000000000 : ℝ)|=(5987453761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016656273/5000000000 : ℝ)|^71 ≤ (6396235420663/50000000000000 : ℝ)^55
        have hw : |(1016656273/5000000000 : ℝ)|=(1016656273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310062_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (734486379/1000000000 : ℝ)*x 0 + (803278901/2000000000 : ℝ)*x 1 + (-493172201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (734486379/1000000000 : ℝ)^71 ≤ (33571226179999/50000000000000 : ℝ)^55 := by
    have hnat : (734486379 : ℕ)^71*50000000000000^55 ≤ 33571226179999^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734486379 1000000000 33571226179999 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803278901/2000000000 : ℝ)^71 ≤ (6160539645291/20000000000000 : ℝ)^55 := by
    have hnat : (803278901 : ℕ)^71*20000000000000^55 ≤ 6160539645291^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803278901 2000000000 6160539645291 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493172201/10000000000 : ℝ)^71 ≤ (82193975629/4000000000000 : ℝ)^55 := by
    have hnat : (493172201 : ℕ)^71*4000000000000^55 ≤ 82193975629^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493172201 10000000000 82193975629 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(734486379/1000000000 : ℝ), (803278901/2000000000 : ℝ), (-493172201/10000000000 : ℝ)] ![(33571226179999/50000000000000 : ℝ), (6160539645291/20000000000000 : ℝ), (82193975629/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(734486379/1000000000 : ℝ)|^71 ≤ (33571226179999/50000000000000 : ℝ)^55
        have hw : |(734486379/1000000000 : ℝ)|=(734486379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803278901/2000000000 : ℝ)|^71 ≤ (6160539645291/20000000000000 : ℝ)^55
        have hw : |(803278901/2000000000 : ℝ)|=(803278901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493172201/10000000000 : ℝ)|^71 ≤ (82193975629/4000000000000 : ℝ)^55
        have hw : |(-493172201/10000000000 : ℝ)|=(493172201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310062_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((7411/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7411/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7399/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7399/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29491/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29491/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((509/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(509/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25651/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4391/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4391/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (7411/10000 : ℝ) ^ (35/8 : ℝ) ≤ (26959451870634004387/100000000000000000000 : ℝ) := by
    have hpowers : (7411/10000 : ℝ)^35 ≤ (26959451870634004387/100000000000000000000 : ℝ)^8 := by
      have hnat : (7411 : ℕ)^35*100000000000000000000^8 ≤ 26959451870634004387^8*10000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7411 10000 26959451870634004387 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7411/10000 : ℝ)) (X := (26959451870634004387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (126959451870634004387/100000000000000000000 : ℝ) ≤ (10560752531842459/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (126959451870634004387/100000000000000000000 : ℝ)^8 ≤ (10560752531842459/10000000000000000 : ℝ)^35 := by
      have hnat : (126959451870634004387 : ℕ)^8*10000000000000000^35 ≤ 10560752531842459^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126959451870634004387 100000000000000000000 10560752531842459 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10560752531842459/10000000000000000 : ℝ)) (X := (126959451870634004387/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (76959451870634004387/50000000000000000000 : ℝ) ≤ (11035946621044167/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (76959451870634004387/50000000000000000000 : ℝ)^8 ≤ (11035946621044167/10000000000000000 : ℝ)^35 := by
      have hnat : (76959451870634004387 : ℕ)^8*10000000000000000^35 ≤ 11035946621044167^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76959451870634004387 50000000000000000000 11035946621044167 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11035946621044167/10000000000000000 : ℝ)) (X := (76959451870634004387/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(560752531842459/7411000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(118798522300427/1852750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (7411/10000 : ℝ)) (alpha := (560752531842459/7411000000000000 : ℝ)) (beta := (118798522300427/1852750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7411/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(560752531842459/7411000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(118798522300427/1852750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (7399/10000 : ℝ) ^ (35/8 : ℝ) ≤ (6692247639680335317/25000000000000000000 : ℝ) := by
    have hpowers : (7399/10000 : ℝ)^35 ≤ (6692247639680335317/25000000000000000000 : ℝ)^8 := by
      have hnat : (7399 : ℕ)^35*25000000000000000000^8 ≤ 6692247639680335317^8*10000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7399 10000 6692247639680335317 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7399/10000 : ℝ)) (X := (6692247639680335317/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (31692247639680335317/25000000000000000000 : ℝ) ≤ (2111425836862517/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (31692247639680335317/25000000000000000000 : ℝ)^8 ≤ (2111425836862517/2000000000000000 : ℝ)^35 := by
      have hnat : (31692247639680335317 : ℕ)^8*2000000000000000^35 ≤ 2111425836862517^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31692247639680335317 25000000000000000000 2111425836862517 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2111425836862517/2000000000000000 : ℝ)) (X := (31692247639680335317/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (19192247639680335317/12500000000000000000 : ℝ) ≤ (11029697897441841/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (19192247639680335317/12500000000000000000 : ℝ)^8 ≤ (11029697897441841/10000000000000000 : ℝ)^35 := by
      have hnat : (19192247639680335317 : ℕ)^8*10000000000000000^35 ≤ 11029697897441841^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19192247639680335317 12500000000000000000 11029697897441841 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11029697897441841/10000000000000000 : ℝ)) (X := (19192247639680335317/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(111425836862517/1479800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(59071089141157/924875000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (7399/10000 : ℝ)) (alpha := (111425836862517/1479800000000000 : ℝ)) (beta := (59071089141157/924875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7399/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(111425836862517/1479800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(59071089141157/924875000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (29491/50000 : ℝ) ^ (35/8 : ℝ) ≤ (496441174149068187/5000000000000000000 : ℝ) := by
    have hpowers : (29491/50000 : ℝ)^35 ≤ (496441174149068187/5000000000000000000 : ℝ)^8 := by
      have hnat : (29491 : ℕ)^35*5000000000000000000^8 ≤ 496441174149068187^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29491 50000 496441174149068187 5000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29491/50000 : ℝ)) (X := (496441174149068187/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (5496441174149068187/5000000000000000000 : ℝ) ≤ (10218730193273673/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5496441174149068187/5000000000000000000 : ℝ)^8 ≤ (10218730193273673/10000000000000000 : ℝ)^35 := by
      have hnat : (5496441174149068187 : ℕ)^8*10000000000000000^35 ≤ 10218730193273673^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5496441174149068187 5000000000000000000 10218730193273673 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10218730193273673/10000000000000000 : ℝ)) (X := (5496441174149068187/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (2996441174149068187/2500000000000000000 : ℝ) ≤ (10422712113842821/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2996441174149068187/2500000000000000000 : ℝ)^8 ≤ (10422712113842821/10000000000000000 : ℝ)^35 := by
      have hnat : (2996441174149068187 : ℕ)^8*10000000000000000^35 ≤ 10422712113842821^35*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2996441174149068187 2500000000000000000 10422712113842821 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10422712113842821/10000000000000000 : ℝ)) (X := (2996441174149068187/2500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(218730193273673/5898200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(50995480142287/1474550000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (29491/50000 : ℝ)) (alpha := (218730193273673/5898200000000000 : ℝ)) (beta := (50995480142287/1474550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29491/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(218730193273673/5898200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(50995480142287/1474550000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-413304221/2500000000 : ℝ)*X 0 0+(2472129351/5000000000 : ℝ)*X 0 1+(-2919234259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1238371371/2500000000 : ℝ)*X 1 0+(-1659821069/10000000000 : ℝ)*X 1 1+(-1165018527/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5226509607/10000000000 : ℝ)*X 2 0+(1309442667/2500000000 : ℝ)*X 2 1+(524785471/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((5562012887/10000000000 : ℝ)*X 0 0+(2771224849/5000000000 : ℝ)*X 0 1+(-47705377/400000000 : ℝ)*X 0 2+(5562012887/10000000000 : ℝ)*X 1 0+(2771224849/5000000000 : ℝ)*X 1 1+(-47705377/400000000 : ℝ)*X 1 2+(5562012887/10000000000 : ℝ)*X 2 0+(2771224849/5000000000 : ℝ)*X 2 1+(-47705377/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1233904583/10000000000 : ℝ)*X 0 0+(1089165717/2500000000 : ℝ)*X 0 1+(-207857903/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2330112599/5000000000 : ℝ)*X 1 0+(-765707561/10000000000 : ℝ)*X 1 1+(-6649636859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4730418223/10000000000 : ℝ)*X 2 0+(1606660507/2500000000 : ℝ)*X 2 1+(524407303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((100768603/200000000 : ℝ)*X 0 0+(6536623771/10000000000 : ℝ)*X 0 1+(-4284753/156250000 : ℝ)*X 0 2+(100768603/200000000 : ℝ)*X 1 0+(6536623771/10000000000 : ℝ)*X 1 1+(-4284753/156250000 : ℝ)*X 1 2+(100768603/200000000 : ℝ)*X 2 0+(6536623771/10000000000 : ℝ)*X 2 1+(-4284753/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-19041421/250000000 : ℝ)*X 0 0+(2333646271/5000000000 : ℝ)*X 0 1+(-3322710191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2186571613/5000000000 : ℝ)*X 1 0+(-611449003/5000000000 : ℝ)*X 1 1+(-1660901377/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6206271279/10000000000 : ℝ)*X 2 0+(2482282493/5000000000 : ℝ)*X 2 1+(527422021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1750389267/2500000000 : ℝ)*X 0 0+(903594683/2000000000 : ℝ)*X 0 1+(-287707523/10000000000 : ℝ)*X 0 2+(1750389267/2500000000 : ℝ)*X 1 0+(903594683/2000000000 : ℝ)*X 1 1+(-287707523/10000000000 : ℝ)*X 1 2+(1750389267/2500000000 : ℝ)*X 2 0+(903594683/2000000000 : ℝ)*X 2 1+(-287707523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-8785943/200000000 : ℝ)*X 0 0+(5690179567/10000000000 : ℝ)*X 0 1+(-1167913417/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1250420871/2000000000 : ℝ)*X 1 0+(-499281917/5000000000 : ℝ)*X 1 1+(-990236289/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2248061661/5000000000 : ℝ)*X 2 0+(5987453761/10000000000 : ℝ)*X 2 1+(1016656273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((734486379/1000000000 : ℝ)*X 0 0+(803278901/2000000000 : ℝ)*X 0 1+(-493172201/10000000000 : ℝ)*X 0 2+(734486379/1000000000 : ℝ)*X 1 0+(803278901/2000000000 : ℝ)*X 1 1+(-493172201/10000000000 : ℝ)*X 1 2+(734486379/1000000000 : ℝ)*X 2 0+(803278901/2000000000 : ℝ)*X 2 1+(-493172201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((509/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(509/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (143833906847413439526762069141/10500708893500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1612373/500000000000 : ℝ)*(base39) + (7279577/1000000000000 : ℝ)*(base49) + (131725156987/1000000000000 : ℝ)*(base60) + (4619801905343/1000000000000 : ℝ)*(major_s2_0) + (4619801905343/1000000000000 : ℝ)*(major_s2_1) + (4619801905343/1000000000000 : ℝ)*(major_s2_2) + (29061909/500000000000 : ℝ)*(sp_s2_0) + (1596038461893/250000000000 : ℝ)*(sp_s2_7) + (638407180953/100000000000 : ℝ)*(sp_s2_8) + (3192054774729/500000000000 : ℝ)*(sp_s2_9) + (571075621979/200000000000 : ℝ)*(sp_s2_13) + (9163547/1000000000000 : ℝ)*(sp_s2_14) + (74662703/500000000000 : ℝ)*(sp_s2_15) + (55792739/500000000000 : ℝ)*(sp_s2_23) + (571075621979/200000000000 : ℝ)*(f.failure) + (798027641867/125000000000 : ℝ)*(f.sum) + (805020048812185323/3117198700000000000000000000000 : ℝ)*base63 + (7000599018309/368637500000000000000000000 : ℝ)*base65 + (78015846651747/115609375000000000000000000 : ℝ)*base67 + (3162565426565119/5898200000000000000000000000 : ℝ)*base69 + (14760457947658262687/218557801000000000000000000000000 : ℝ)*base71 + (100368331140089/1852750000000000000000000000 : ℝ)*base72 + (766130326834331/1479800000000000000000000000 : ℝ)*base75 + (4324726762988737/7411000000000000000000000000 : ℝ)*base77 + (11784899057693106861/13708497250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (11653/20000000000000000 : ℝ)*base86 + (11653/20000000000000000 : ℝ)*base88 + (11653/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25651/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (237387160001215285335387/20241550000000000000000000000 : ℝ) := by norm_num
    linear_combination (40269/250000000000 : ℝ)*(base49) + (810217/500000000000 : ℝ)*(base60) + (929756882313/200000000000 : ℝ)*(major_s2_0) + (929756882313/200000000000 : ℝ)*(major_s2_1) + (929756882313/200000000000 : ℝ)*(major_s2_2) + (42733843/1000000000000 : ℝ)*(sp_s2_2) + (9624289/1000000000000 : ℝ)*(sp_s2_6) + (2384787/40000000000 : ℝ)*(sp_s2_7) + (65836333/1000000000000 : ℝ)*(sp_s2_8) + (642421385913/100000000000 : ℝ)*(sp_s2_14) + (803025955309/125000000000 : ℝ)*(sp_s2_15) + (3212115372481/500000000000 : ℝ)*(sp_s2_16) + (2873167975171/1000000000000 : ℝ)*(sp_s2_20) + (14229453/125000000000 : ℝ)*(sp_s2_27) + (718322858771/250000000000 : ℝ)*(f.failure) + (1284854695761/200000000000 : ℝ)*(f.sum) + (18908512715900173/89062820000000000000000000000 : ℝ)*base62 + (1769596019369/21065000000000000000000000 : ℝ)*base64 + (4423630651449/13212500000000000000000000 : ℝ)*base67 + (10205069156717/168520000000000000000000000 : ℝ)*base68 + (1335526548790970989/6244508600000000000000000000000 : ℝ)*base70 + (18620332564787/185275000000000000000000000 : ℝ)*base72 + (8889871445437/42280000000000000000000000 : ℝ)*base74 + (35398566361807/1482200000000000000000000000 : ℝ)*base77 + (183703996341164003/391671350000000000000000000000 : ℝ)*base79 + (11403/25000000000000000 : ℝ)*base87 + (11403/25000000000000000 : ℝ)*base89 + (11403/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4391/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4391/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8736213984360366078317324277/750050635250000000000000000000000 : ℝ) := by norm_num
    linear_combination (613671/62500000000 : ℝ)*(base11) + (21809537919/50000000000 : ℝ)*(base39) + (1780143533903/500000000000 : ℝ)*(major_s2_0) + (1780143533903/500000000000 : ℝ)*(major_s2_1) + (1780143533903/500000000000 : ℝ)*(major_s2_2) + (12656533/500000000000 : ℝ)*(sp_s2_0) + (7674113/1000000000000 : ℝ)*(sp_s2_1) + (7080349/1000000000000 : ℝ)*(sp_s2_2) + (566721/8000000000 : ℝ)*(sp_s2_9) + (434911/100000000000 : ℝ)*(sp_s2_20) + (4920015279401/1000000000000 : ℝ)*(sp_s2_21) + (4920042737091/1000000000000 : ℝ)*(sp_s2_22) + (491997249073/100000000000 : ℝ)*(sp_s2_23) + (220051549279/100000000000 : ℝ)*(sp_s2_27) + (22005198419/10000000000 : ℝ)*(f.failure) + (1230012602801/250000000000 : ℝ)*(f.sum) + (45788034869221459/222657050000000000000000000000 : ℝ)*base63 + (221803180232611/210650000000000000000000000 : ℝ)*base65 + (124847239735963/264250000000000000000000000 : ℝ)*base66 + (144861582681807/421300000000000000000000000 : ℝ)*base69 + (3310282263402780311/15611271500000000000000000000000 : ℝ)*base71 + (35855048911557/115796875000000000000000000 : ℝ)*base73 + (43240552273633/105700000000000000000000000 : ℝ)*base75 + (826468631478377/3705500000000000000000000000 : ℝ)*base77 + (223869195741993779/489589187500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (733/1000000000000000 : ℝ)*base86 + (733/1000000000000000 : ℝ)*base88 + (733/1000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((7411/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7411/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7399/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7399/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29491/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29491/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((509/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(509/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25651/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4391/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4391/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310062_s2 p hpa hpb X hX hprev1

#print axioms solution
