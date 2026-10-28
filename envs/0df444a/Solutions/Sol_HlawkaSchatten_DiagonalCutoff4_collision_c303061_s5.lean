-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303061_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:58:16.935319+00:00
-- url     : https://prove2.me/submissions/22a15045-2eb3-434b-b9b0-6351ac5aee63

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
theorem collision_support_c303061_s5_s5_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2279489911/10000000000 : ℝ)*x 0 + (2296423419/5000000000 : ℝ)*x 1 + (739280559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2279489911/10000000000 : ℝ)^33 ≤ (7100938224893/50000000000000 : ℝ)^25 := by
    have hnat : (2279489911 : ℕ)^33*50000000000000^25 ≤ 7100938224893^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279489911 10000000000 7100938224893 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296423419/5000000000 : ℝ)^33 ≤ (17902686030827/50000000000000 : ℝ)^25 := by
    have hnat : (2296423419 : ℕ)^33*50000000000000^25 ≤ 17902686030827^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296423419 5000000000 17902686030827 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739280559/1250000000 : ℝ)^33 ≤ (24996375735731/50000000000000 : ℝ)^25 := by
    have hnat : (739280559 : ℕ)^33*50000000000000^25 ≤ 24996375735731^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739280559 1250000000 24996375735731 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2279489911/10000000000 : ℝ), (2296423419/5000000000 : ℝ), (739280559/1250000000 : ℝ)] ![(7100938224893/50000000000000 : ℝ), (17902686030827/50000000000000 : ℝ), (24996375735731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2279489911/10000000000 : ℝ)|^33 ≤ (7100938224893/50000000000000 : ℝ)^25
        have hw : |(-2279489911/10000000000 : ℝ)|=(2279489911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296423419/5000000000 : ℝ)|^33 ≤ (17902686030827/50000000000000 : ℝ)^25
        have hw : |(2296423419/5000000000 : ℝ)|=(2296423419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(739280559/1250000000 : ℝ)|^33 ≤ (24996375735731/50000000000000 : ℝ)^25
        have hw : |(739280559/1250000000 : ℝ)|=(739280559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1187756363/2500000000 : ℝ)*x 0 + (-1194656089/5000000000 : ℝ)*x 1 + (5684560887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1187756363/2500000000 : ℝ)^33 ≤ (37442023477241/100000000000000 : ℝ)^25 := by
    have hnat : (1187756363 : ℕ)^33*100000000000000^25 ≤ 37442023477241^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187756363 2500000000 37442023477241 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194656089/5000000000 : ℝ)^33 ≤ (472248128219/3125000000000 : ℝ)^25 := by
    have hnat : (1194656089 : ℕ)^33*3125000000000^25 ≤ 472248128219^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194656089 5000000000 472248128219 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5684560887/10000000000 : ℝ)^33 ≤ (47446036406723/100000000000000 : ℝ)^25 := by
    have hnat : (5684560887 : ℕ)^33*100000000000000^25 ≤ 47446036406723^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684560887 10000000000 47446036406723 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1187756363/2500000000 : ℝ), (-1194656089/5000000000 : ℝ), (5684560887/10000000000 : ℝ)] ![(37442023477241/100000000000000 : ℝ), (472248128219/3125000000000 : ℝ), (47446036406723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1187756363/2500000000 : ℝ)|^33 ≤ (37442023477241/100000000000000 : ℝ)^25
        have hw : |(1187756363/2500000000 : ℝ)|=(1187756363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1194656089/5000000000 : ℝ)|^33 ≤ (472248128219/3125000000000 : ℝ)^25
        have hw : |(-1194656089/5000000000 : ℝ)|=(1194656089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5684560887/10000000000 : ℝ)|^33 ≤ (47446036406723/100000000000000 : ℝ)^25
        have hw : |(5684560887/10000000000 : ℝ)|=(5684560887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4839827901/10000000000 : ℝ)*x 0 + (6297641853/10000000000 : ℝ)*x 1 + (-1379267603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4839827901/10000000000 : ℝ)^33 ≤ (38368559364517/100000000000000 : ℝ)^25 := by
    have hnat : (4839827901 : ℕ)^33*100000000000000^25 ≤ 38368559364517^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839827901 10000000000 38368559364517 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6297641853/10000000000 : ℝ)^33 ≤ (27157194941467/50000000000000 : ℝ)^25 := by
    have hnat : (6297641853 : ℕ)^33*50000000000000^25 ≤ 27157194941467^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6297641853 10000000000 27157194941467 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379267603/10000000000 : ℝ)^33 ≤ (1829262685197/25000000000000 : ℝ)^25 := by
    have hnat : (1379267603 : ℕ)^33*25000000000000^25 ≤ 1829262685197^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379267603 10000000000 1829262685197 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4839827901/10000000000 : ℝ), (6297641853/10000000000 : ℝ), (-1379267603/10000000000 : ℝ)] ![(38368559364517/100000000000000 : ℝ), (27157194941467/50000000000000 : ℝ), (1829262685197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4839827901/10000000000 : ℝ)|^33 ≤ (38368559364517/100000000000000 : ℝ)^25
        have hw : |(4839827901/10000000000 : ℝ)|=(4839827901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6297641853/10000000000 : ℝ)|^33 ≤ (27157194941467/50000000000000 : ℝ)^25
        have hw : |(6297641853/10000000000 : ℝ)|=(6297641853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1379267603/10000000000 : ℝ)|^33 ≤ (1829262685197/25000000000000 : ℝ)^25
        have hw : |(-1379267603/10000000000 : ℝ)|=(1379267603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2999195509/5000000000 : ℝ)*x 0 + (3138518813/10000000000 : ℝ)*x 1 + (750148501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2999195509/5000000000 : ℝ)^33 ≤ (10186755811009/20000000000000 : ℝ)^25 := by
    have hnat : (2999195509 : ℕ)^33*20000000000000^25 ≤ 10186755811009^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999195509 5000000000 10186755811009 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3138518813/10000000000 : ℝ)^33 ≤ (5415226926029/25000000000000 : ℝ)^25 := by
    have hnat : (3138518813 : ℕ)^33*25000000000000^25 ≤ 5415226926029^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138518813 10000000000 5415226926029 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750148501/2000000000 : ℝ)^33 ≤ (27405313224579/100000000000000 : ℝ)^25 := by
    have hnat : (750148501 : ℕ)^33*100000000000000^25 ≤ 27405313224579^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750148501 2000000000 27405313224579 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2999195509/5000000000 : ℝ), (3138518813/10000000000 : ℝ), (750148501/2000000000 : ℝ)] ![(10186755811009/20000000000000 : ℝ), (5415226926029/25000000000000 : ℝ), (27405313224579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2999195509/5000000000 : ℝ)|^33 ≤ (10186755811009/20000000000000 : ℝ)^25
        have hw : |(2999195509/5000000000 : ℝ)|=(2999195509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3138518813/10000000000 : ℝ)|^33 ≤ (5415226926029/25000000000000 : ℝ)^25
        have hw : |(3138518813/10000000000 : ℝ)|=(3138518813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750148501/2000000000 : ℝ)|^33 ≤ (27405313224579/100000000000000 : ℝ)^25
        have hw : |(750148501/2000000000 : ℝ)|=(750148501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1112069223/5000000000 : ℝ)*x 0 + (476522961/1250000000 : ℝ)*x 1 + (6640576649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1112069223/5000000000 : ℝ)^33 ≤ (13748445575921/100000000000000 : ℝ)^25 := by
    have hnat : (1112069223 : ℕ)^33*100000000000000^25 ≤ 13748445575921^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112069223 5000000000 13748445575921 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476522961/1250000000 : ℝ)^33 ≤ (13999723073239/50000000000000 : ℝ)^25 := by
    have hnat : (476522961 : ℕ)^33*50000000000000^25 ≤ 13999723073239^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476522961 1250000000 13999723073239 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6640576649/10000000000 : ℝ)^33 ≤ (58252108260567/100000000000000 : ℝ)^25 := by
    have hnat : (6640576649 : ℕ)^33*100000000000000^25 ≤ 58252108260567^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6640576649 10000000000 58252108260567 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1112069223/5000000000 : ℝ), (476522961/1250000000 : ℝ), (6640576649/10000000000 : ℝ)] ![(13748445575921/100000000000000 : ℝ), (13999723073239/50000000000000 : ℝ), (58252108260567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1112069223/5000000000 : ℝ)|^33 ≤ (13748445575921/100000000000000 : ℝ)^25
        have hw : |(-1112069223/5000000000 : ℝ)|=(1112069223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(476522961/1250000000 : ℝ)|^33 ≤ (13999723073239/50000000000000 : ℝ)^25
        have hw : |(476522961/1250000000 : ℝ)|=(476522961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6640576649/10000000000 : ℝ)|^33 ≤ (58252108260567/100000000000000 : ℝ)^25
        have hw : |(6640576649/10000000000 : ℝ)|=(6640576649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4283982561/10000000000 : ℝ)*x 0 + (-877115627/5000000000 : ℝ)*x 1 + (3278557089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283982561/10000000000 : ℝ)^33 ≤ (16330856428637/50000000000000 : ℝ)^25 := by
    have hnat : (4283982561 : ℕ)^33*50000000000000^25 ≤ 16330856428637^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283982561 10000000000 16330856428637 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877115627/5000000000 : ℝ)^33 ≤ (1256332652751/12500000000000 : ℝ)^25 := by
    have hnat : (877115627 : ℕ)^33*12500000000000^25 ≤ 1256332652751^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877115627 5000000000 1256332652751 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3278557089/5000000000 : ℝ)^33 ≤ (14321906477299/25000000000000 : ℝ)^25 := by
    have hnat : (3278557089 : ℕ)^33*25000000000000^25 ≤ 14321906477299^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3278557089 5000000000 14321906477299 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283982561/10000000000 : ℝ), (-877115627/5000000000 : ℝ), (3278557089/5000000000 : ℝ)] ![(16330856428637/50000000000000 : ℝ), (1256332652751/12500000000000 : ℝ), (14321906477299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283982561/10000000000 : ℝ)|^33 ≤ (16330856428637/50000000000000 : ℝ)^25
        have hw : |(4283982561/10000000000 : ℝ)|=(4283982561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-877115627/5000000000 : ℝ)|^33 ≤ (1256332652751/12500000000000 : ℝ)^25
        have hw : |(-877115627/5000000000 : ℝ)|=(877115627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3278557089/5000000000 : ℝ)|^33 ≤ (14321906477299/25000000000000 : ℝ)^25
        have hw : |(3278557089/5000000000 : ℝ)|=(3278557089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (218684979/500000000 : ℝ)*x 0 + (7140020999/10000000000 : ℝ)*x 1 + (-144842677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218684979/500000000 : ℝ)^33 ≤ (8391906207807/25000000000000 : ℝ)^25 := by
    have hnat : (218684979 : ℕ)^33*25000000000000^25 ≤ 8391906207807^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218684979 500000000 8391906207807 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7140020999/10000000000 : ℝ)^33 ≤ (16025933423431/25000000000000 : ℝ)^25 := by
    have hnat : (7140020999 : ℕ)^33*25000000000000^25 ≤ 16025933423431^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7140020999 10000000000 16025933423431 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144842677/2500000000 : ℝ)^33 ≤ (232864145813/10000000000000 : ℝ)^25 := by
    have hnat : (144842677 : ℕ)^33*10000000000000^25 ≤ 232864145813^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144842677 2500000000 232864145813 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218684979/500000000 : ℝ), (7140020999/10000000000 : ℝ), (-144842677/2500000000 : ℝ)] ![(8391906207807/25000000000000 : ℝ), (16025933423431/25000000000000 : ℝ), (232864145813/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218684979/500000000 : ℝ)|^33 ≤ (8391906207807/25000000000000 : ℝ)^25
        have hw : |(218684979/500000000 : ℝ)|=(218684979/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7140020999/10000000000 : ℝ)|^33 ≤ (16025933423431/25000000000000 : ℝ)^25
        have hw : |(7140020999/10000000000 : ℝ)|=(7140020999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-144842677/2500000000 : ℝ)|^33 ≤ (232864145813/10000000000000 : ℝ)^25
        have hw : |(-144842677/2500000000 : ℝ)|=(144842677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5840132979/10000000000 : ℝ)*x 0 + (2282197603/5000000000 : ℝ)*x 1 + (2414148263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5840132979/10000000000 : ℝ)^33 ≤ (9833497399033/20000000000000 : ℝ)^25 := by
    have hnat : (5840132979 : ℕ)^33*20000000000000^25 ≤ 9833497399033^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5840132979 10000000000 9833497399033 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282197603/5000000000 : ℝ)^33 ≤ (3551287866539/10000000000000 : ℝ)^25 := by
    have hnat : (2282197603 : ℕ)^33*10000000000000^25 ≤ 3551287866539^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282197603 5000000000 3551287866539 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2414148263/10000000000 : ℝ)^33 ≤ (15319634317451/100000000000000 : ℝ)^25 := by
    have hnat : (2414148263 : ℕ)^33*100000000000000^25 ≤ 15319634317451^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414148263 10000000000 15319634317451 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5840132979/10000000000 : ℝ), (2282197603/5000000000 : ℝ), (2414148263/10000000000 : ℝ)] ![(9833497399033/20000000000000 : ℝ), (3551287866539/10000000000000 : ℝ), (15319634317451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5840132979/10000000000 : ℝ)|^33 ≤ (9833497399033/20000000000000 : ℝ)^25
        have hw : |(5840132979/10000000000 : ℝ)|=(5840132979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282197603/5000000000 : ℝ)|^33 ≤ (3551287866539/10000000000000 : ℝ)^25
        have hw : |(2282197603/5000000000 : ℝ)|=(2282197603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2414148263/10000000000 : ℝ)|^33 ≤ (15319634317451/100000000000000 : ℝ)^25
        have hw : |(2414148263/10000000000 : ℝ)|=(2414148263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1245855391/10000000000 : ℝ)*x 0 + (4559570813/10000000000 : ℝ)*x 1 + (828851387/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1245855391/10000000000 : ℝ)^33 ≤ (3198801445399/50000000000000 : ℝ)^25 := by
    have hnat : (1245855391 : ℕ)^33*50000000000000^25 ≤ 3198801445399^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245855391 10000000000 3198801445399 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4559570813/10000000000 : ℝ)^33 ≤ (8865834957921/25000000000000 : ℝ)^25 := by
    have hnat : (4559570813 : ℕ)^33*25000000000000^25 ≤ 8865834957921^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559570813 10000000000 8865834957921 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828851387/1250000000 : ℝ)^33 ≤ (14534764316097/25000000000000 : ℝ)^25 := by
    have hnat : (828851387 : ℕ)^33*25000000000000^25 ≤ 14534764316097^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828851387 1250000000 14534764316097 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1245855391/10000000000 : ℝ), (4559570813/10000000000 : ℝ), (828851387/1250000000 : ℝ)] ![(3198801445399/50000000000000 : ℝ), (8865834957921/25000000000000 : ℝ), (14534764316097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1245855391/10000000000 : ℝ)|^33 ≤ (3198801445399/50000000000000 : ℝ)^25
        have hw : |(-1245855391/10000000000 : ℝ)|=(1245855391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4559570813/10000000000 : ℝ)|^33 ≤ (8865834957921/25000000000000 : ℝ)^25
        have hw : |(4559570813/10000000000 : ℝ)|=(4559570813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828851387/1250000000 : ℝ)|^33 ≤ (14534764316097/25000000000000 : ℝ)^25
        have hw : |(828851387/1250000000 : ℝ)|=(828851387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1039782311/2500000000 : ℝ)*x 0 + (-386335683/2000000000 : ℝ)*x 1 + (654734579/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039782311/2500000000 : ℝ)^33 ≤ (31411103177151/100000000000000 : ℝ)^25 := by
    have hnat : (1039782311 : ℕ)^33*100000000000000^25 ≤ 31411103177151^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039782311 2500000000 31411103177151 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386335683/2000000000 : ℝ)^33 ≤ (11413897589679/100000000000000 : ℝ)^25 := by
    have hnat : (386335683 : ℕ)^33*100000000000000^25 ≤ 11413897589679^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386335683 2000000000 11413897589679 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654734579/1000000000 : ℝ)^33 ≤ (1143499984251/2000000000000 : ℝ)^25 := by
    have hnat : (654734579 : ℕ)^33*2000000000000^25 ≤ 1143499984251^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654734579 1000000000 1143499984251 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039782311/2500000000 : ℝ), (-386335683/2000000000 : ℝ), (654734579/1000000000 : ℝ)] ![(31411103177151/100000000000000 : ℝ), (11413897589679/100000000000000 : ℝ), (1143499984251/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039782311/2500000000 : ℝ)|^33 ≤ (31411103177151/100000000000000 : ℝ)^25
        have hw : |(1039782311/2500000000 : ℝ)|=(1039782311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-386335683/2000000000 : ℝ)|^33 ≤ (11413897589679/100000000000000 : ℝ)^25
        have hw : |(-386335683/2000000000 : ℝ)|=(386335683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654734579/1000000000 : ℝ)|^33 ≤ (1143499984251/2000000000000 : ℝ)^25
        have hw : |(654734579/1000000000 : ℝ)|=(654734579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5946689249/10000000000 : ℝ)*x 0 + (708507443/1250000000 : ℝ)*x 1 + (-294568623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5946689249/10000000000 : ℝ)^33 ≤ (50355083770411/100000000000000 : ℝ)^25 := by
    have hnat : (5946689249 : ℕ)^33*100000000000000^25 ≤ 50355083770411^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946689249 10000000000 50355083770411 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708507443/1250000000 : ℝ)^33 ≤ (11816079978217/25000000000000 : ℝ)^25 := by
    have hnat : (708507443 : ℕ)^33*25000000000000^25 ≤ 11816079978217^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708507443 1250000000 11816079978217 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294568623/5000000000 : ℝ)^33 ≤ (1190298149071/50000000000000 : ℝ)^25 := by
    have hnat : (294568623 : ℕ)^33*50000000000000^25 ≤ 1190298149071^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294568623 5000000000 1190298149071 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5946689249/10000000000 : ℝ), (708507443/1250000000 : ℝ), (-294568623/5000000000 : ℝ)] ![(50355083770411/100000000000000 : ℝ), (11816079978217/25000000000000 : ℝ), (1190298149071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5946689249/10000000000 : ℝ)|^33 ≤ (50355083770411/100000000000000 : ℝ)^25
        have hw : |(5946689249/10000000000 : ℝ)|=(5946689249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708507443/1250000000 : ℝ)|^33 ≤ (11816079978217/25000000000000 : ℝ)^25
        have hw : |(708507443/1250000000 : ℝ)|=(708507443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-294568623/5000000000 : ℝ)|^33 ≤ (1190298149071/50000000000000 : ℝ)^25
        have hw : |(-294568623/5000000000 : ℝ)|=(294568623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7285299831/10000000000 : ℝ)*x 0 + (140303197/500000000 : ℝ)*x 1 + (608441151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7285299831/10000000000 : ℝ)^33 ≤ (65831023573683/100000000000000 : ℝ)^25 := by
    have hnat : (7285299831 : ℕ)^33*100000000000000^25 ≤ 65831023573683^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7285299831 10000000000 65831023573683 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140303197/500000000 : ℝ)^33 ≤ (2335601771069/12500000000000 : ℝ)^25 := by
    have hnat : (140303197 : ℕ)^33*12500000000000^25 ≤ 2335601771069^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140303197 500000000 2335601771069 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608441151/2500000000 : ℝ)^33 ≤ (1935520280043/12500000000000 : ℝ)^25 := by
    have hnat : (608441151 : ℕ)^33*12500000000000^25 ≤ 1935520280043^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608441151 2500000000 1935520280043 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7285299831/10000000000 : ℝ), (140303197/500000000 : ℝ), (608441151/2500000000 : ℝ)] ![(65831023573683/100000000000000 : ℝ), (2335601771069/12500000000000 : ℝ), (1935520280043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7285299831/10000000000 : ℝ)|^33 ≤ (65831023573683/100000000000000 : ℝ)^25
        have hw : |(7285299831/10000000000 : ℝ)|=(7285299831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140303197/500000000 : ℝ)|^33 ≤ (2335601771069/12500000000000 : ℝ)^25
        have hw : |(140303197/500000000 : ℝ)|=(140303197/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(608441151/2500000000 : ℝ)|^33 ≤ (1935520280043/12500000000000 : ℝ)^25
        have hw : |(608441151/2500000000 : ℝ)|=(608441151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1209678451/10000000000 : ℝ)*x 0 + (2696173079/5000000000 : ℝ)*x 1 + (2939194519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1209678451/10000000000 : ℝ)^33 ≤ (3076765029791/50000000000000 : ℝ)^25 := by
    have hnat : (1209678451 : ℕ)^33*50000000000000^25 ≤ 3076765029791^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209678451 10000000000 3076765029791 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696173079/5000000000 : ℝ)^33 ≤ (44253400485211/100000000000000 : ℝ)^25 := by
    have hnat : (2696173079 : ℕ)^33*100000000000000^25 ≤ 44253400485211^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696173079 5000000000 44253400485211 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2939194519/5000000000 : ℝ)^33 ≤ (49593069437131/100000000000000 : ℝ)^25 := by
    have hnat : (2939194519 : ℕ)^33*100000000000000^25 ≤ 49593069437131^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939194519 5000000000 49593069437131 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1209678451/10000000000 : ℝ), (2696173079/5000000000 : ℝ), (2939194519/5000000000 : ℝ)] ![(3076765029791/50000000000000 : ℝ), (44253400485211/100000000000000 : ℝ), (49593069437131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1209678451/10000000000 : ℝ)|^33 ≤ (3076765029791/50000000000000 : ℝ)^25
        have hw : |(-1209678451/10000000000 : ℝ)|=(1209678451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696173079/5000000000 : ℝ)|^33 ≤ (44253400485211/100000000000000 : ℝ)^25
        have hw : |(2696173079/5000000000 : ℝ)|=(2696173079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2939194519/5000000000 : ℝ)|^33 ≤ (49593069437131/100000000000000 : ℝ)^25
        have hw : |(2939194519/5000000000 : ℝ)|=(2939194519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5893148953/10000000000 : ℝ)*x 0 + (-1321753597/10000000000 : ℝ)*x 1 + (5306468647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5893148953/10000000000 : ℝ)^33 ≤ (49757504637193/100000000000000 : ℝ)^25 := by
    have hnat : (5893148953 : ℕ)^33*100000000000000^25 ≤ 49757504637193^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5893148953 10000000000 49757504637193 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1321753597/10000000000 : ℝ)^33 ≤ (691701410479/10000000000000 : ℝ)^25 := by
    have hnat : (1321753597 : ℕ)^33*10000000000000^25 ≤ 691701410479^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321753597 10000000000 691701410479 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5306468647/10000000000 : ℝ)^33 ≤ (43325481242673/100000000000000 : ℝ)^25 := by
    have hnat : (5306468647 : ℕ)^33*100000000000000^25 ≤ 43325481242673^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306468647 10000000000 43325481242673 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5893148953/10000000000 : ℝ), (-1321753597/10000000000 : ℝ), (5306468647/10000000000 : ℝ)] ![(49757504637193/100000000000000 : ℝ), (691701410479/10000000000000 : ℝ), (43325481242673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5893148953/10000000000 : ℝ)|^33 ≤ (49757504637193/100000000000000 : ℝ)^25
        have hw : |(5893148953/10000000000 : ℝ)|=(5893148953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1321753597/10000000000 : ℝ)|^33 ≤ (691701410479/10000000000000 : ℝ)^25
        have hw : |(-1321753597/10000000000 : ℝ)|=(1321753597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5306468647/10000000000 : ℝ)|^33 ≤ (43325481242673/100000000000000 : ℝ)^25
        have hw : |(5306468647/10000000000 : ℝ)|=(5306468647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4127367461/10000000000 : ℝ)*x 0 + (7077298411/10000000000 : ℝ)*x 1 + (-558859693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127367461/10000000000 : ℝ)^33 ≤ (31094855253129/100000000000000 : ℝ)^25 := by
    have hnat : (4127367461 : ℕ)^33*100000000000000^25 ≤ 31094855253129^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127367461 10000000000 31094855253129 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7077298411/10000000000 : ℝ)^33 ≤ (7920181304289/12500000000000 : ℝ)^25 := by
    have hnat : (7077298411 : ℕ)^33*12500000000000^25 ≤ 7920181304289^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7077298411 10000000000 7920181304289 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558859693/5000000000 : ℝ)^33 ≤ (5543694307457/100000000000000 : ℝ)^25 := by
    have hnat : (558859693 : ℕ)^33*100000000000000^25 ≤ 5543694307457^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558859693 5000000000 5543694307457 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127367461/10000000000 : ℝ), (7077298411/10000000000 : ℝ), (-558859693/5000000000 : ℝ)] ![(31094855253129/100000000000000 : ℝ), (7920181304289/12500000000000 : ℝ), (5543694307457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127367461/10000000000 : ℝ)|^33 ≤ (31094855253129/100000000000000 : ℝ)^25
        have hw : |(4127367461/10000000000 : ℝ)|=(4127367461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7077298411/10000000000 : ℝ)|^33 ≤ (7920181304289/12500000000000 : ℝ)^25
        have hw : |(7077298411/10000000000 : ℝ)|=(7077298411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558859693/5000000000 : ℝ)|^33 ≤ (5543694307457/100000000000000 : ℝ)^25
        have hw : |(-558859693/5000000000 : ℝ)|=(558859693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303061_s5_s5_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7529271759/10000000000 : ℝ)*x 0 + (2385356677/10000000000 : ℝ)*x 1 + (314294639/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7529271759/10000000000 : ℝ)^33 ≤ (34378262889957/50000000000000 : ℝ)^25 := by
    have hnat : (7529271759 : ℕ)^33*50000000000000^25 ≤ 34378262889957^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7529271759 10000000000 34378262889957 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2385356677/10000000000 : ℝ)^33 ≤ (15078925379647/100000000000000 : ℝ)^25 := by
    have hnat : (2385356677 : ℕ)^33*100000000000000^25 ≤ 15078925379647^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385356677 10000000000 15078925379647 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314294639/1250000000 : ℝ)^33 ≤ (4041137207343/25000000000000 : ℝ)^25 := by
    have hnat : (314294639 : ℕ)^33*25000000000000^25 ≤ 4041137207343^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314294639 1250000000 4041137207343 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7529271759/10000000000 : ℝ), (2385356677/10000000000 : ℝ), (314294639/1250000000 : ℝ)] ![(34378262889957/50000000000000 : ℝ), (15078925379647/100000000000000 : ℝ), (4041137207343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7529271759/10000000000 : ℝ)|^33 ≤ (34378262889957/50000000000000 : ℝ)^25
        have hw : |(7529271759/10000000000 : ℝ)|=(7529271759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2385356677/10000000000 : ℝ)|^33 ≤ (15078925379647/100000000000000 : ℝ)^25
        have hw : |(2385356677/10000000000 : ℝ)|=(2385356677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314294639/1250000000 : ℝ)|^33 ≤ (4041137207343/25000000000000 : ℝ)^25
        have hw : |(314294639/1250000000 : ℝ)|=(314294639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303061_s5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((55537/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55537/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61477/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61477/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7023/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7023/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((36349/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36349/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8379/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8379/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38389/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38389/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (55537/100000 : ℝ) ^ (131/32 : ℝ) ≤ (450146907717196159/5000000000000000000 : ℝ) := by
    have hpowers : (55537/100000 : ℝ)^131 ≤ (450146907717196159/5000000000000000000 : ℝ)^32 := by
      have hnat : (55537 : ℕ)^131*5000000000000000000^32 ≤ 450146907717196159^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55537 100000 450146907717196159 5000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55537/100000 : ℝ)) (X := (450146907717196159/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (5450146907717196159/5000000000000000000 : ℝ) ≤ (51064045051197/50000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (5450146907717196159/5000000000000000000 : ℝ)^32 ≤ (51064045051197/50000000000000 : ℝ)^131 := by
      have hnat : (5450146907717196159 : ℕ)^32*50000000000000^131 ≤ 51064045051197^131*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5450146907717196159 5000000000000000000 51064045051197 50000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (51064045051197/50000000000000 : ℝ)) (X := (5450146907717196159/5000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (2950146907717196159/2500000000000000000 : ℝ) ≤ (2082544269770421/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2950146907717196159/2500000000000000000 : ℝ)^32 ≤ (2082544269770421/2000000000000000 : ℝ)^131 := by
      have hnat : (2950146907717196159 : ℕ)^32*2000000000000000^131 ≤ 2082544269770421^131*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2950146907717196159 2500000000000000000 2082544269770421 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2082544269770421/2000000000000000 : ℝ)) (X := (2950146907717196159/2500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1064045051197/27768500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(39982467722541/1110740000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (55537/100000 : ℝ)) (alpha := (1064045051197/27768500000000 : ℝ)) (beta := (39982467722541/1110740000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (55537/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1064045051197/27768500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(39982467722541/1110740000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (61477/100000 : ℝ) ^ (131/32 : ℝ) ≤ (1364716611150034477/10000000000000000000 : ℝ) := by
    have hpowers : (61477/100000 : ℝ)^131 ≤ (1364716611150034477/10000000000000000000 : ℝ)^32 := by
      have hnat : (61477 : ℕ)^131*10000000000000000000^32 ≤ 1364716611150034477^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61477 100000 1364716611150034477 10000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61477/100000 : ℝ)) (X := (1364716611150034477/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (11364716611150034477/10000000000000000000 : ℝ) ≤ (10317430902635409/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (11364716611150034477/10000000000000000000 : ℝ)^32 ≤ (10317430902635409/10000000000000000 : ℝ)^131 := by
      have hnat : (11364716611150034477 : ℕ)^32*10000000000000000^131 ≤ 10317430902635409^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11364716611150034477 10000000000000000000 10317430902635409 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10317430902635409/10000000000000000 : ℝ)) (X := (11364716611150034477/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (6364716611150034477/5000000000000000000 : ℝ) ≤ (10607235592392239/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (6364716611150034477/5000000000000000000 : ℝ)^32 ≤ (10607235592392239/10000000000000000 : ℝ)^131 := by
      have hnat : (6364716611150034477 : ℕ)^32*10000000000000000^131 ≤ 10607235592392239^131*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6364716611150034477 5000000000000000000 10607235592392239 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10607235592392239/10000000000000000 : ℝ)) (X := (6364716611150034477/5000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(317430902635409/6147700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(28980468975683/614770000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (61477/100000 : ℝ)) (alpha := (317430902635409/6147700000000000 : ℝ)) (beta := (28980468975683/614770000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (61477/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(317430902635409/6147700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(28980468975683/614770000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (7023/12500 : ℝ) ^ (131/32 : ℝ) ≤ (4720052317414829277/50000000000000000000 : ℝ) := by
    have hpowers : (7023/12500 : ℝ)^131 ≤ (4720052317414829277/50000000000000000000 : ℝ)^32 := by
      have hnat : (7023 : ℕ)^131*50000000000000000000^32 ≤ 4720052317414829277^32*12500^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7023 12500 4720052317414829277 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7023/12500 : ℝ)) (X := (4720052317414829277/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (54720052317414829277/50000000000000000000 : ℝ) ≤ (1022279923903207/1000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (54720052317414829277/50000000000000000000 : ℝ)^32 ≤ (1022279923903207/1000000000000000 : ℝ)^131 := by
      have hnat : (54720052317414829277 : ℕ)^32*1000000000000000^131 ≤ 1022279923903207^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54720052317414829277 50000000000000000000 1022279923903207 1000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1022279923903207/1000000000000000 : ℝ)) (X := (54720052317414829277/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (29720052317414829277/25000000000000000000 : ℝ) ≤ (2086302936454531/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (29720052317414829277/25000000000000000000 : ℝ)^32 ≤ (2086302936454531/2000000000000000 : ℝ)^131 := by
      have hnat : (29720052317414829277 : ℕ)^32*2000000000000000^131 ≤ 2086302936454531^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29720052317414829277 25000000000000000000 2086302936454531 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2086302936454531/2000000000000000 : ℝ)) (X := (29720052317414829277/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7426641301069/187280000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(41743088648117/1123680000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (7023/12500 : ℝ)) (alpha := (7426641301069/187280000000000 : ℝ)) (beta := (41743088648117/1123680000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7023/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7426641301069/187280000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(41743088648117/1123680000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2279489911/10000000000 : ℝ)*X 0 0+(2296423419/5000000000 : ℝ)*X 0 1+(739280559/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((1187756363/2500000000 : ℝ)*X 1 0+(-1194656089/5000000000 : ℝ)*X 1 1+(5684560887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((4839827901/10000000000 : ℝ)*X 2 0+(6297641853/10000000000 : ℝ)*X 2 1+(-1379267603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((2999195509/5000000000 : ℝ)*X 0 0+(3138518813/10000000000 : ℝ)*X 0 1+(750148501/2000000000 : ℝ)*X 0 2+(2999195509/5000000000 : ℝ)*X 1 0+(3138518813/10000000000 : ℝ)*X 1 1+(750148501/2000000000 : ℝ)*X 1 2+(2999195509/5000000000 : ℝ)*X 2 0+(3138518813/10000000000 : ℝ)*X 2 1+(750148501/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-1112069223/5000000000 : ℝ)*X 0 0+(476522961/1250000000 : ℝ)*X 0 1+(6640576649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4283982561/10000000000 : ℝ)*X 1 0+(-877115627/5000000000 : ℝ)*X 1 1+(3278557089/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((218684979/500000000 : ℝ)*X 2 0+(7140020999/10000000000 : ℝ)*X 2 1+(-144842677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((5840132979/10000000000 : ℝ)*X 0 0+(2282197603/5000000000 : ℝ)*X 0 1+(2414148263/10000000000 : ℝ)*X 0 2+(5840132979/10000000000 : ℝ)*X 1 0+(2282197603/5000000000 : ℝ)*X 1 1+(2414148263/10000000000 : ℝ)*X 1 2+(5840132979/10000000000 : ℝ)*X 2 0+(2282197603/5000000000 : ℝ)*X 2 1+(2414148263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-1245855391/10000000000 : ℝ)*X 0 0+(4559570813/10000000000 : ℝ)*X 0 1+(828851387/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((1039782311/2500000000 : ℝ)*X 1 0+(-386335683/2000000000 : ℝ)*X 1 1+(654734579/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((5946689249/10000000000 : ℝ)*X 2 0+(708507443/1250000000 : ℝ)*X 2 1+(-294568623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((7285299831/10000000000 : ℝ)*X 0 0+(140303197/500000000 : ℝ)*X 0 1+(608441151/2500000000 : ℝ)*X 0 2+(7285299831/10000000000 : ℝ)*X 1 0+(140303197/500000000 : ℝ)*X 1 1+(608441151/2500000000 : ℝ)*X 1 2+(7285299831/10000000000 : ℝ)*X 2 0+(140303197/500000000 : ℝ)*X 2 1+(608441151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-1209678451/10000000000 : ℝ)*X 0 0+(2696173079/5000000000 : ℝ)*X 0 1+(2939194519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((5893148953/10000000000 : ℝ)*X 1 0+(-1321753597/10000000000 : ℝ)*X 1 1+(5306468647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((4127367461/10000000000 : ℝ)*X 2 0+(7077298411/10000000000 : ℝ)*X 2 1+(-558859693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((7529271759/10000000000 : ℝ)*X 0 0+(2385356677/10000000000 : ℝ)*X 0 1+(314294639/1250000000 : ℝ)*X 0 2+(7529271759/10000000000 : ℝ)*X 1 0+(2385356677/10000000000 : ℝ)*X 1 1+(314294639/1250000000 : ℝ)*X 1 2+(7529271759/10000000000 : ℝ)*X 2 0+(2385356677/10000000000 : ℝ)*X 2 1+(314294639/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303061_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((36349/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36349/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20933266496671963042872302271331/1598550983361800000000000000000000000 : ℝ) := by norm_num
    linear_combination (981557/1000000000000 : ℝ)*(base50) + (137702065437/200000000000 : ℝ)*(base59) + (2288804514983/500000000000 : ℝ)*(major_s5_0) + (2288804514983/500000000000 : ℝ)*(major_s5_1) + (2288804514983/500000000000 : ℝ)*(major_s5_2) + (40864413/1000000000000 : ℝ)*(sp_s5_0) + (3890337/125000000000 : ℝ)*(sp_s5_1) + (42565379/1000000000000 : ℝ)*(sp_s5_6) + (6111954488509/1000000000000 : ℝ)*(sp_s5_7) + (6111575878297/1000000000000 : ℝ)*(sp_s5_8) + (1527967267327/250000000000 : ℝ)*(sp_s5_9) + (121727031063/40000000000 : ℝ)*(sp_s5_13) + (48543991/125000000000 : ℝ)*(sp_s5_15) + (126283613/1000000000000 : ℝ)*(sp_s5_23) + (3043218341953/1000000000000 : ℝ)*(f.failure) + (6111995352921/1000000000000 : ℝ)*(f.sum) + (16798848029392939097/28783531400000000000000000000000 : ℝ)*base62 + (550476774467803/561840000000000000000000000 : ℝ)*base64 + (298171852126091/614770000000000000000000000 : ℝ)*base66 + (7871903068881/18728000000000000000000000 : ℝ)*base68 + (3940726636567427279/6240581616000000000000000000000 : ℝ)*base70 + (92569107426643/555370000000000000000000000 : ℝ)*base72 + (2235335811919253/3073850000000000000000000000 : ℝ)*base74 + (23680679932951/138842500000000000000000000 : ℝ)*base76 + (119060706046812011/6828496298000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1487/5000000000000000 : ℝ)*base86 + (1487/5000000000000000 : ℝ)*base88 + (1487/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8379/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8379/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10693736908673469447650017003269/3197101966723600000000000000000000000 : ℝ) := by norm_num
    linear_combination (635211/1000000000000 : ℝ)*(base49) + (319981866797/1000000000000 : ℝ)*(base59) + (4411214695077/1000000000000 : ℝ)*(major_s5_0) + (4411214695077/1000000000000 : ℝ)*(major_s5_1) + (4411214695077/1000000000000 : ℝ)*(major_s5_2) + (5461307/500000000000 : ℝ)*(sp_s5_2) + (6307249/1000000000000 : ℝ)*(sp_s5_6) + (16317097/1000000000000 : ℝ)*(sp_s5_7) + (8355033/1000000000000 : ℝ)*(sp_s5_8) + (23559253749/4000000000 : ℝ)*(sp_s5_14) + (2944910699657/500000000000 : ℝ)*(sp_s5_15) + (2944909415867/500000000000 : ℝ)*(sp_s5_16) + (2932547166261/1000000000000 : ℝ)*(sp_s5_20) + (900947/20000000000 : ℝ)*(sp_s5_27) + (146629926043/50000000000 : ℝ)*(f.failure) + (5889829754347/1000000000000 : ℝ)*(f.sum) + (7284493208602432123/57567062800000000000000000000000 : ℝ)*base62 + (296399719438131/374560000000000000000000000 : ℝ)*base64 + (1995683014943/614770000000000000000000000 : ℝ)*base66 + (88444243453343/187280000000000000000000000 : ℝ)*base68 + (8609811287032762851/20801938720000000000000000000000 : ℝ)*base70 + (98565355088609/222148000000000000000000000 : ℝ)*base72 + (6153620373632817/6147700000000000000000000000 : ℝ)*base74 + (22975587101857/22214800000000000000000000 : ℝ)*base76 + (30326656985569747789/68284962980000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (153/250000000000000 : ℝ)*base87 + (153/250000000000000 : ℝ)*base89 + (153/250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38389/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38389/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (243604980649454213061805911/34142481490000000000000000000000 : ℝ) := by norm_num
    linear_combination (252033/50000000000 : ℝ)*(base15) + (131626355531/500000000000 : ℝ)*(base40) + (42526678269/125000000000 : ℝ)*(base59) + (4036439421567/1000000000000 : ℝ)*(major_s5_0) + (4036439421567/1000000000000 : ℝ)*(major_s5_1) + (4036439421567/1000000000000 : ℝ)*(major_s5_2) + (56029/1000000000000 : ℝ)*(sp_s5_0) + (12183783/100000000000 : ℝ)*(sp_s5_2) + (1600133/50000000000 : ℝ)*(sp_s5_9) + (155060093/500000000000 : ℝ)*(sp_s5_20) + (538943044311/100000000000 : ℝ)*(sp_s5_21) + (5389425458479/1000000000000 : ℝ)*(sp_s5_22) + (5389276658649/1000000000000 : ℝ)*(sp_s5_23) + (167695990343/62500000000 : ℝ)*(sp_s5_27) + (1341722982837/500000000000 : ℝ)*(f.failure) + (5389430499139/1000000000000 : ℝ)*(f.sum) + (969377722224135073/57567062800000000000000000000000 : ℝ)*base62 + (54479399363399/374560000000000000000000000 : ℝ)*base65 + (6608061711249/24590800000000000000000000 : ℝ)*base67 + (47942891669163/187280000000000000000000000 : ℝ)*base69 + (10755967846247795417/20801938720000000000000000000000 : ℝ)*base70 + (151767974679037/222148000000000000000000000 : ℝ)*base73 + (1695979995359613/6147700000000000000000000000 : ℝ)*base75 + (15423546347413/111074000000000000000000000 : ℝ)*base76 + (5209307796720971053/13656992596000000000000000000000 : ℝ)*base79 + (423/2500000000000000 : ℝ)*base86 + (423/2500000000000000 : ℝ)*base88 + (423/2500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((55537/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55537/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61477/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61477/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7023/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7023/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((36349/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36349/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8379/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8379/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38389/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38389/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303061_s5 p hpa hpb X hX hprev4

#print axioms solution
