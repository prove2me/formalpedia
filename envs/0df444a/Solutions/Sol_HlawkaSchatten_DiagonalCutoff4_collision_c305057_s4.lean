-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305057_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:30:15.942521+00:00
-- url     : https://prove2.me/submissions/a38c9dac-4a74-4503-9e65-9d5d51027114

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
theorem collision_support_c305057_s4_s4_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3546261343/10000000000 : ℝ)*x 0 + (3546210573/10000000000 : ℝ)*x 1 + (5789014399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3546261343/10000000000 : ℝ)^67 ≤ (5123330087681/20000000000000 : ℝ)^51 := by
    have hnat : (3546261343 : ℕ)^67*20000000000000^51 ≤ 5123330087681^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3546261343 10000000000 5123330087681 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3546210573/10000000000 : ℝ)^67 ≤ (25616168643261/100000000000000 : ℝ)^51 := by
    have hnat : (3546210573 : ℕ)^67*100000000000000^51 ≤ 25616168643261^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3546210573 10000000000 25616168643261 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5789014399/10000000000 : ℝ)^67 ≤ (48767180897769/100000000000000 : ℝ)^51 := by
    have hnat : (5789014399 : ℕ)^67*100000000000000^51 ≤ 48767180897769^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5789014399 10000000000 48767180897769 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3546261343/10000000000 : ℝ), (3546210573/10000000000 : ℝ), (5789014399/10000000000 : ℝ)] ![(5123330087681/20000000000000 : ℝ), (25616168643261/100000000000000 : ℝ), (48767180897769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3546261343/10000000000 : ℝ)|^67 ≤ (5123330087681/20000000000000 : ℝ)^51
        have hw : |(-3546261343/10000000000 : ℝ)|=(3546261343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3546210573/10000000000 : ℝ)|^67 ≤ (25616168643261/100000000000000 : ℝ)^51
        have hw : |(3546210573/10000000000 : ℝ)|=(3546210573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5789014399/10000000000 : ℝ)|^67 ≤ (48767180897769/100000000000000 : ℝ)^51
        have hw : |(5789014399/10000000000 : ℝ)|=(5789014399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3546227583/10000000000 : ℝ)*x 0 + (-3546176813/10000000000 : ℝ)*x 1 + (5789072297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3546227583/10000000000 : ℝ)^67 ≤ (25616330063847/100000000000000 : ℝ)^51 := by
    have hnat : (3546227583 : ℕ)^67*100000000000000^51 ≤ 25616330063847^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3546227583 10000000000 25616330063847 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3546176813/10000000000 : ℝ)^67 ≤ (12807924135071/50000000000000 : ℝ)^51 := by
    have hnat : (3546176813 : ℕ)^67*50000000000000^51 ≤ 12807924135071^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3546176813 10000000000 12807924135071 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5789072297/10000000000 : ℝ)^67 ≤ (48767821652603/100000000000000 : ℝ)^51 := by
    have hnat : (5789072297 : ℕ)^67*100000000000000^51 ≤ 48767821652603^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5789072297 10000000000 48767821652603 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3546227583/10000000000 : ℝ), (-3546176813/10000000000 : ℝ), (5789072297/10000000000 : ℝ)] ![(25616330063847/100000000000000 : ℝ), (12807924135071/50000000000000 : ℝ), (48767821652603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3546227583/10000000000 : ℝ)|^67 ≤ (25616330063847/100000000000000 : ℝ)^51
        have hw : |(3546227583/10000000000 : ℝ)|=(3546227583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3546176813/10000000000 : ℝ)|^67 ≤ (12807924135071/50000000000000 : ℝ)^51
        have hw : |(-3546176813/10000000000 : ℝ)|=(3546176813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5789072297/10000000000 : ℝ)|^67 ≤ (48767821652603/100000000000000 : ℝ)^51
        have hw : |(5789072297/10000000000 : ℝ)|=(5789072297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2790210739/5000000000 : ℝ)*x 0 + (2790235837/5000000000 : ℝ)*x 1 + (-265795591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2790210739/5000000000 : ℝ)^67 ≤ (4647185222307/10000000000000 : ℝ)^51 := by
    have hnat : (2790210739 : ℕ)^67*10000000000000^51 ≤ 4647185222307^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790210739 5000000000 4647185222307 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2790235837/5000000000 : ℝ)^67 ≤ (4647240138109/10000000000000 : ℝ)^51 := by
    have hnat : (2790235837 : ℕ)^67*10000000000000^51 ≤ 4647240138109^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790235837 5000000000 4647240138109 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265795591/2000000000 : ℝ)^67 ≤ (3527873192153/50000000000000 : ℝ)^51 := by
    have hnat : (265795591 : ℕ)^67*50000000000000^51 ≤ 3527873192153^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265795591 2000000000 3527873192153 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2790210739/5000000000 : ℝ), (2790235837/5000000000 : ℝ), (-265795591/2000000000 : ℝ)] ![(4647185222307/10000000000000 : ℝ), (4647240138109/10000000000000 : ℝ), (3527873192153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2790210739/5000000000 : ℝ)|^67 ≤ (4647185222307/10000000000000 : ℝ)^51
        have hw : |(2790210739/5000000000 : ℝ)|=(2790210739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2790235837/5000000000 : ℝ)|^67 ≤ (4647240138109/10000000000000 : ℝ)^51
        have hw : |(2790235837/5000000000 : ℝ)|=(2790235837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265795591/2000000000 : ℝ)|^67 ≤ (3527873192153/50000000000000 : ℝ)^51
        have hw : |(-265795591/2000000000 : ℝ)|=(265795591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (44921079/100000000 : ℝ)*x 0 + (4492148307/10000000000 : ℝ)*x 1 + (250622693/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44921079/100000000 : ℝ)^67 ≤ (34947405693179/100000000000000 : ℝ)^51 := by
    have hnat : (44921079 : ℕ)^67*100000000000000^51 ≤ 34947405693179^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44921079 100000000 34947405693179 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492148307/10000000000 : ℝ)^67 ≤ (17473909335443/50000000000000 : ℝ)^51 := by
    have hnat : (4492148307 : ℕ)^67*50000000000000^51 ≤ 17473909335443^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492148307 10000000000 17473909335443 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250622693/625000000 : ℝ)^67 ≤ (30104775611973/100000000000000 : ℝ)^51 := by
    have hnat : (250622693 : ℕ)^67*100000000000000^51 ≤ 30104775611973^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250622693 625000000 30104775611973 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44921079/100000000 : ℝ), (4492148307/10000000000 : ℝ), (250622693/625000000 : ℝ)] ![(34947405693179/100000000000000 : ℝ), (17473909335443/50000000000000 : ℝ), (30104775611973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44921079/100000000 : ℝ)|^67 ≤ (34947405693179/100000000000000 : ℝ)^51
        have hw : |(44921079/100000000 : ℝ)|=(44921079/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492148307/10000000000 : ℝ)|^67 ≤ (17473909335443/50000000000000 : ℝ)^51
        have hw : |(4492148307/10000000000 : ℝ)|=(4492148307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250622693/625000000 : ℝ)|^67 ≤ (30104775611973/100000000000000 : ℝ)^51
        have hw : |(250622693/625000000 : ℝ)|=(250622693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3518376371/10000000000 : ℝ)*x 0 + (1706779919/5000000000 : ℝ)*x 1 + (5925466901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3518376371/10000000000 : ℝ)^67 ≤ (396130548781/1562500000000 : ℝ)^51 := by
    have hnat : (3518376371 : ℕ)^67*1562500000000^51 ≤ 396130548781^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3518376371 10000000000 396130548781 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1706779919/5000000000 : ℝ)^67 ≤ (6091199577591/25000000000000 : ℝ)^51 := by
    have hnat : (1706779919 : ℕ)^67*25000000000000^51 ≤ 6091199577591^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706779919 5000000000 6091199577591 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5925466901/10000000000 : ℝ)^67 ≤ (6285355818927/12500000000000 : ℝ)^51 := by
    have hnat : (5925466901 : ℕ)^67*12500000000000^51 ≤ 6285355818927^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925466901 10000000000 6285355818927 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3518376371/10000000000 : ℝ), (1706779919/5000000000 : ℝ), (5925466901/10000000000 : ℝ)] ![(396130548781/1562500000000 : ℝ), (6091199577591/25000000000000 : ℝ), (6285355818927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3518376371/10000000000 : ℝ)|^67 ≤ (396130548781/1562500000000 : ℝ)^51
        have hw : |(-3518376371/10000000000 : ℝ)|=(3518376371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1706779919/5000000000 : ℝ)|^67 ≤ (6091199577591/25000000000000 : ℝ)^51
        have hw : |(1706779919/5000000000 : ℝ)|=(1706779919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5925466901/10000000000 : ℝ)|^67 ≤ (6285355818927/12500000000000 : ℝ)^51
        have hw : |(5925466901/10000000000 : ℝ)|=(5925466901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (351833441/1000000000 : ℝ)*x 0 + (-3413519127/10000000000 : ℝ)*x 1 + (237021471/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351833441/1000000000 : ℝ)^67 ≤ (3168994738371/12500000000000 : ℝ)^51 := by
    have hnat : (351833441 : ℕ)^67*12500000000000^51 ≤ 3168994738371^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351833441 1000000000 3168994738371 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3413519127/10000000000 : ℝ)^67 ≤ (12182208283769/50000000000000 : ℝ)^51 := by
    have hnat : (3413519127 : ℕ)^67*50000000000000^51 ≤ 12182208283769^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3413519127 10000000000 12182208283769 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237021471/400000000 : ℝ)^67 ≤ (50283625517079/100000000000000 : ℝ)^51 := by
    have hnat : (237021471 : ℕ)^67*100000000000000^51 ≤ 50283625517079^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237021471 400000000 50283625517079 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(351833441/1000000000 : ℝ), (-3413519127/10000000000 : ℝ), (237021471/400000000 : ℝ)] ![(3168994738371/12500000000000 : ℝ), (12182208283769/50000000000000 : ℝ), (50283625517079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(351833441/1000000000 : ℝ)|^67 ≤ (3168994738371/12500000000000 : ℝ)^51
        have hw : |(351833441/1000000000 : ℝ)|=(351833441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3413519127/10000000000 : ℝ)|^67 ≤ (12182208283769/50000000000000 : ℝ)^51
        have hw : |(-3413519127/10000000000 : ℝ)|=(3413519127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237021471/400000000 : ℝ)|^67 ≤ (50283625517079/100000000000000 : ℝ)^51
        have hw : |(237021471/400000000 : ℝ)|=(237021471/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2753253327/5000000000 : ℝ)*x 0 + (5738161799/10000000000 : ℝ)*x 1 + (-47761573/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753253327/5000000000 : ℝ)^67 ≤ (114162225373/250000000000 : ℝ)^51 := by
    have hnat : (2753253327 : ℕ)^67*250000000000^51 ≤ 114162225373^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753253327 5000000000 114162225373 250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5738161799/10000000000 : ℝ)^67 ≤ (48205175146629/100000000000000 : ℝ)^51 := by
    have hnat : (5738161799 : ℕ)^67*100000000000000^51 ≤ 48205175146629^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5738161799 10000000000 48205175146629 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47761573/400000000 : ℝ)^67 ≤ (6129934692211/100000000000000 : ℝ)^51 := by
    have hnat : (47761573 : ℕ)^67*100000000000000^51 ≤ 6129934692211^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47761573 400000000 6129934692211 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753253327/5000000000 : ℝ), (5738161799/10000000000 : ℝ), (-47761573/400000000 : ℝ)] ![(114162225373/250000000000 : ℝ), (48205175146629/100000000000000 : ℝ), (6129934692211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753253327/5000000000 : ℝ)|^67 ≤ (114162225373/250000000000 : ℝ)^51
        have hw : |(2753253327/5000000000 : ℝ)|=(2753253327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5738161799/10000000000 : ℝ)|^67 ≤ (48205175146629/100000000000000 : ℝ)^51
        have hw : |(5738161799/10000000000 : ℝ)|=(5738161799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47761573/400000000 : ℝ)|^67 ≤ (6129934692211/100000000000000 : ℝ)^51
        have hw : |(-47761573/400000000 : ℝ)|=(47761573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_12 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4528779393/10000000000 : ℝ)*x 0 + (471930219/1000000000 : ℝ)*x 1 + (373159471/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4528779393/10000000000 : ℝ)^67 ≤ (35322683367849/100000000000000 : ℝ)^51 := by
    have hnat : (4528779393 : ℕ)^67*100000000000000^51 ≤ 35322683367849^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528779393 10000000000 35322683367849 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471930219/1000000000 : ℝ)^67 ≤ (18643821687127/50000000000000 : ℝ)^51 := by
    have hnat : (471930219 : ℕ)^67*50000000000000^51 ≤ 18643821687127^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471930219 1000000000 18643821687127 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373159471/1000000000 : ℝ)^67 ≤ (5477934647421/20000000000000 : ℝ)^51 := by
    have hnat : (373159471 : ℕ)^67*20000000000000^51 ≤ 5477934647421^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373159471 1000000000 5477934647421 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4528779393/10000000000 : ℝ), (471930219/1000000000 : ℝ), (373159471/1000000000 : ℝ)] ![(35322683367849/100000000000000 : ℝ), (18643821687127/50000000000000 : ℝ), (5477934647421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4528779393/10000000000 : ℝ)|^67 ≤ (35322683367849/100000000000000 : ℝ)^51
        have hw : |(4528779393/10000000000 : ℝ)|=(4528779393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(471930219/1000000000 : ℝ)|^67 ≤ (18643821687127/50000000000000 : ℝ)^51
        have hw : |(471930219/1000000000 : ℝ)|=(471930219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373159471/1000000000 : ℝ)|^67 ≤ (5477934647421/20000000000000 : ℝ)^51
        have hw : |(373159471/1000000000 : ℝ)|=(373159471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-136544061/400000000 : ℝ)*x 0 + (1759167877/5000000000 : ℝ)*x 1 + (2962733163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136544061/400000000 : ℝ)^67 ≤ (12182594603261/50000000000000 : ℝ)^51 := by
    have hnat : (136544061 : ℕ)^67*50000000000000^51 ≤ 12182594603261^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136544061 400000000 12182594603261 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759167877/5000000000 : ℝ)^67 ≤ (633799265741/2500000000000 : ℝ)^51 := by
    have hnat : (1759167877 : ℕ)^67*2500000000000^51 ≤ 633799265741^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759167877 5000000000 633799265741 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2962733163/5000000000 : ℝ)^67 ≤ (50282840141243/100000000000000 : ℝ)^51 := by
    have hnat : (2962733163 : ℕ)^67*100000000000000^51 ≤ 50282840141243^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2962733163 5000000000 50282840141243 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136544061/400000000 : ℝ), (1759167877/5000000000 : ℝ), (2962733163/5000000000 : ℝ)] ![(12182594603261/50000000000000 : ℝ), (633799265741/2500000000000 : ℝ), (50282840141243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136544061/400000000 : ℝ)|^67 ≤ (12182594603261/50000000000000 : ℝ)^51
        have hw : |(-136544061/400000000 : ℝ)|=(136544061/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1759167877/5000000000 : ℝ)|^67 ≤ (633799265741/2500000000000 : ℝ)^51
        have hw : |(1759167877/5000000000 : ℝ)|=(1759167877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2962733163/5000000000 : ℝ)|^67 ≤ (50282840141243/100000000000000 : ℝ)^51
        have hw : |(2962733163/5000000000 : ℝ)|=(2962733163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1706779993/5000000000 : ℝ)*x 0 + (-3518292941/10000000000 : ℝ)*x 1 + (5925537621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706779993/5000000000 : ℝ)^67 ≤ (6091199924537/25000000000000 : ℝ)^51 := by
    have hnat : (1706779993 : ℕ)^67*25000000000000^51 ≤ 6091199924537^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706779993 5000000000 6091199924537 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3518292941/10000000000 : ℝ)^67 ≤ (25351565350827/100000000000000 : ℝ)^51 := by
    have hnat : (3518292941 : ℕ)^67*100000000000000^51 ≤ 25351565350827^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3518292941 10000000000 25351565350827 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5925537621/10000000000 : ℝ)^67 ≤ (5028363494843/10000000000000 : ℝ)^51 := by
    have hnat : (5925537621 : ℕ)^67*10000000000000^51 ≤ 5028363494843^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925537621 10000000000 5028363494843 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1706779993/5000000000 : ℝ), (-3518292941/10000000000 : ℝ), (5925537621/10000000000 : ℝ)] ![(6091199924537/25000000000000 : ℝ), (25351565350827/100000000000000 : ℝ), (5028363494843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1706779993/5000000000 : ℝ)|^67 ≤ (6091199924537/25000000000000 : ℝ)^51
        have hw : |(1706779993/5000000000 : ℝ)|=(1706779993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3518292941/10000000000 : ℝ)|^67 ≤ (25351565350827/100000000000000 : ℝ)^51
        have hw : |(-3518292941/10000000000 : ℝ)|=(3518292941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5925537621/10000000000 : ℝ)|^67 ≤ (5028363494843/10000000000000 : ℝ)^51
        have hw : |(5925537621/10000000000 : ℝ)|=(5925537621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5738101517/10000000000 : ℝ)*x 0 + (5506567691/10000000000 : ℝ)*x 1 + (-1194039371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5738101517/10000000000 : ℝ)^67 ≤ (24102254927209/50000000000000 : ℝ)^51 := by
    have hnat : (5738101517 : ℕ)^67*50000000000000^51 ≤ 24102254927209^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5738101517 10000000000 24102254927209 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506567691/10000000000 : ℝ)^67 ≤ (45665555123423/100000000000000 : ℝ)^51 := by
    have hnat : (5506567691 : ℕ)^67*100000000000000^51 ≤ 45665555123423^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506567691 10000000000 45665555123423 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194039371/10000000000 : ℝ)^67 ≤ (6129935002453/100000000000000 : ℝ)^51 := by
    have hnat : (1194039371 : ℕ)^67*100000000000000^51 ≤ 6129935002453^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194039371 10000000000 6129935002453 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5738101517/10000000000 : ℝ), (5506567691/10000000000 : ℝ), (-1194039371/10000000000 : ℝ)] ![(24102254927209/50000000000000 : ℝ), (45665555123423/100000000000000 : ℝ), (6129935002453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5738101517/10000000000 : ℝ)|^67 ≤ (24102254927209/50000000000000 : ℝ)^51
        have hw : |(5738101517/10000000000 : ℝ)|=(5738101517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506567691/10000000000 : ℝ)|^67 ≤ (45665555123423/100000000000000 : ℝ)^51
        have hw : |(5506567691/10000000000 : ℝ)|=(5506567691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1194039371/10000000000 : ℝ)|^67 ≤ (6129935002453/100000000000000 : ℝ)^51
        have hw : |(-1194039371/10000000000 : ℝ)|=(1194039371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_18 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (471925257/1000000000 : ℝ)*x 0 + (4528829553/10000000000 : ℝ)*x 1 + (1865797411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471925257/1000000000 : ℝ)^67 ≤ (37287128326119/100000000000000 : ℝ)^51 := by
    have hnat : (471925257 : ℕ)^67*100000000000000^51 ≤ 37287128326119^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471925257 1000000000 37287128326119 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528829553/10000000000 : ℝ)^67 ≤ (35323197335081/100000000000000 : ℝ)^51 := by
    have hnat : (4528829553 : ℕ)^67*100000000000000^51 ≤ 35323197335081^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528829553 10000000000 35323197335081 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865797411/5000000000 : ℝ)^67 ≤ (6847418579271/25000000000000 : ℝ)^51 := by
    have hnat : (1865797411 : ℕ)^67*25000000000000^51 ≤ 6847418579271^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865797411 5000000000 6847418579271 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(471925257/1000000000 : ℝ), (4528829553/10000000000 : ℝ), (1865797411/5000000000 : ℝ)] ![(37287128326119/100000000000000 : ℝ), (35323197335081/100000000000000 : ℝ), (6847418579271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(471925257/1000000000 : ℝ)|^67 ≤ (37287128326119/100000000000000 : ℝ)^51
        have hw : |(471925257/1000000000 : ℝ)|=(471925257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528829553/10000000000 : ℝ)|^67 ≤ (35323197335081/100000000000000 : ℝ)^51
        have hw : |(4528829553/10000000000 : ℝ)|=(4528829553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1865797411/5000000000 : ℝ)|^67 ≤ (6847418579271/25000000000000 : ℝ)^51
        have hw : |(1865797411/5000000000 : ℝ)|=(1865797411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_19 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-712594877/2000000000 : ℝ)*x 0 + (353102147/1000000000 : ℝ)*x 1 + (578768819/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (712594877/2000000000 : ℝ)^67 ≤ (12887685343203/50000000000000 : ℝ)^51 := by
    have hnat : (712594877 : ℕ)^67*50000000000000^51 ≤ 12887685343203^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712594877 2000000000 12887685343203 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353102147/1000000000 : ℝ)^67 ≤ (25472124955467/100000000000000 : ℝ)^51 := by
    have hnat : (353102147 : ℕ)^67*100000000000000^51 ≤ 25472124955467^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353102147 1000000000 25472124955467 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578768819/1000000000 : ℝ)^67 ≤ (48752504346679/100000000000000 : ℝ)^51 := by
    have hnat : (578768819 : ℕ)^67*100000000000000^51 ≤ 48752504346679^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578768819 1000000000 48752504346679 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-712594877/2000000000 : ℝ), (353102147/1000000000 : ℝ), (578768819/1000000000 : ℝ)] ![(12887685343203/50000000000000 : ℝ), (25472124955467/100000000000000 : ℝ), (48752504346679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-712594877/2000000000 : ℝ)|^67 ≤ (12887685343203/50000000000000 : ℝ)^51
        have hw : |(-712594877/2000000000 : ℝ)|=(712594877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(353102147/1000000000 : ℝ)|^67 ≤ (25472124955467/100000000000000 : ℝ)^51
        have hw : |(353102147/1000000000 : ℝ)|=(353102147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(578768819/1000000000 : ℝ)|^67 ≤ (48752504346679/100000000000000 : ℝ)^51
        have hw : |(578768819/1000000000 : ℝ)|=(578768819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3531023091/10000000000 : ℝ)*x 0 + (-1781445741/5000000000 : ℝ)*x 1 + (5787757999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3531023091/10000000000 : ℝ)^67 ≤ (12736070158817/50000000000000 : ℝ)^51 := by
    have hnat : (3531023091 : ℕ)^67*50000000000000^51 ≤ 12736070158817^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3531023091 10000000000 12736070158817 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1781445741/5000000000 : ℝ)^67 ≤ (3221822849569/12500000000000 : ℝ)^51 := by
    have hnat : (1781445741 : ℕ)^67*12500000000000^51 ≤ 3221822849569^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781445741 5000000000 3221822849569 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5787757999/10000000000 : ℝ)^67 ≤ (48753276864789/100000000000000 : ℝ)^51 := by
    have hnat : (5787757999 : ℕ)^67*100000000000000^51 ≤ 48753276864789^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5787757999 10000000000 48753276864789 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3531023091/10000000000 : ℝ), (-1781445741/5000000000 : ℝ), (5787757999/10000000000 : ℝ)] ![(12736070158817/50000000000000 : ℝ), (3221822849569/12500000000000 : ℝ), (48753276864789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3531023091/10000000000 : ℝ)|^67 ≤ (12736070158817/50000000000000 : ℝ)^51
        have hw : |(3531023091/10000000000 : ℝ)|=(3531023091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1781445741/5000000000 : ℝ)|^67 ≤ (3221822849569/12500000000000 : ℝ)^51
        have hw : |(-1781445741/5000000000 : ℝ)|=(1781445741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5787757999/10000000000 : ℝ)|^67 ≤ (48753276864789/100000000000000 : ℝ)^51
        have hw : |(5787757999/10000000000 : ℝ)|=(5787757999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1118107381/2000000000 : ℝ)*x 0 + (1392799451/2500000000 : ℝ)*x 1 + (-1327649463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118107381/2000000000 : ℝ)^67 ≤ (46582549068823/100000000000000 : ℝ)^51 := by
    have hnat : (1118107381 : ℕ)^67*100000000000000^51 ≤ 46582549068823^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118107381 2000000000 46582549068823 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392799451/2500000000 : ℝ)^67 ≤ (370967752101/800000000000 : ℝ)^51 := by
    have hnat : (1392799451 : ℕ)^67*800000000000^51 ≤ 370967752101^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392799451 2500000000 370967752101 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1327649463/10000000000 : ℝ)^67 ≤ (7046481913131/100000000000000 : ℝ)^51 := by
    have hnat : (1327649463 : ℕ)^67*100000000000000^51 ≤ 7046481913131^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327649463 10000000000 7046481913131 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1118107381/2000000000 : ℝ), (1392799451/2500000000 : ℝ), (-1327649463/10000000000 : ℝ)] ![(46582549068823/100000000000000 : ℝ), (370967752101/800000000000 : ℝ), (7046481913131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1118107381/2000000000 : ℝ)|^67 ≤ (46582549068823/100000000000000 : ℝ)^51
        have hw : |(1118107381/2000000000 : ℝ)|=(1118107381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1392799451/2500000000 : ℝ)|^67 ≤ (370967752101/800000000000 : ℝ)^51
        have hw : |(1392799451/2500000000 : ℝ)|=(1392799451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1327649463/10000000000 : ℝ)|^67 ≤ (7046481913131/100000000000000 : ℝ)^51
        have hw : |(-1327649463/10000000000 : ℝ)|=(1327649463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s4_s4_25 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1118431451/2500000000 : ℝ)*x 0 + (141053401/312500000 : ℝ)*x 1 + (2003319933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118431451/2500000000 : ℝ)^67 ≤ (34759653380307/100000000000000 : ℝ)^51 := by
    have hnat : (1118431451 : ℕ)^67*100000000000000^51 ≤ 34759653380307^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118431451 2500000000 34759653380307 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141053401/312500000 : ℝ)^67 ≤ (7033668592549/20000000000000 : ℝ)^51 := by
    have hnat : (141053401 : ℕ)^67*20000000000000^51 ≤ 7033668592549^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141053401 312500000 7033668592549 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003319933/5000000000 : ℝ)^67 ≤ (30072003643501/100000000000000 : ℝ)^51 := by
    have hnat : (2003319933 : ℕ)^67*100000000000000^51 ≤ 30072003643501^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003319933 5000000000 30072003643501 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1118431451/2500000000 : ℝ), (141053401/312500000 : ℝ), (2003319933/5000000000 : ℝ)] ![(34759653380307/100000000000000 : ℝ), (7033668592549/20000000000000 : ℝ), (30072003643501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1118431451/2500000000 : ℝ)|^67 ≤ (34759653380307/100000000000000 : ℝ)^51
        have hw : |(1118431451/2500000000 : ℝ)|=(1118431451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141053401/312500000 : ℝ)|^67 ≤ (7033668592549/20000000000000 : ℝ)^51
        have hw : |(141053401/312500000 : ℝ)|=(141053401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2003319933/5000000000 : ℝ)|^67 ≤ (30072003643501/100000000000000 : ℝ)^51
        have hw : |(2003319933/5000000000 : ℝ)|=(2003319933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305057_s4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((7453/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7453/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59619/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12271/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(12271/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21469/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21469/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21469/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21469/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(243/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(243/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (7453/12500 : ℝ) ^ (133/32 : ℝ) ≤ (466287713781285123/4000000000000000000 : ℝ) := by
    have hpowers : (7453/12500 : ℝ)^133 ≤ (466287713781285123/4000000000000000000 : ℝ)^32 := by
      have hnat : (7453 : ℕ)^133*4000000000000000000^32 ≤ 466287713781285123^32*12500^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7453 12500 466287713781285123 4000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7453/12500 : ℝ)) (X := (466287713781285123/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (4466287713781285123/4000000000000000000 : ℝ) ≤ (10268845347194599/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (4466287713781285123/4000000000000000000 : ℝ)^32 ≤ (10268845347194599/10000000000000000 : ℝ)^133 := by
      have hnat : (4466287713781285123 : ℕ)^32*10000000000000000^133 ≤ 10268845347194599^133*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4466287713781285123 4000000000000000000 10268845347194599 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10268845347194599/10000000000000000 : ℝ)) (X := (4466287713781285123/4000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (2466287713781285123/2000000000000000000 : ℝ) ≤ (2629287352021111/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2466287713781285123/2000000000000000000 : ℝ)^32 ≤ (2629287352021111/2500000000000000 : ℝ)^133 := by
      have hnat : (2466287713781285123 : ℕ)^32*2500000000000000^133 ≤ 2629287352021111^133*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2466287713781285123 2000000000000000000 2629287352021111 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2629287352021111/2500000000000000 : ℝ)) (X := (2466287713781285123/2000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(268845347194599/5962400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(49660812177969/1192480000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (7453/12500 : ℝ)) (alpha := (268845347194599/5962400000000000 : ℝ)) (beta := (49660812177969/1192480000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7453/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(268845347194599/5962400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(49660812177969/1192480000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (59619/100000 : ℝ) ^ (133/32 : ℝ) ≤ (5826565201773545567/50000000000000000000 : ℝ) := by
    have hpowers : (59619/100000 : ℝ)^133 ≤ (5826565201773545567/50000000000000000000 : ℝ)^32 := by
      have hnat : (59619 : ℕ)^133*50000000000000000000^32 ≤ 5826565201773545567^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59619 100000 5826565201773545567 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59619/100000 : ℝ)) (X := (5826565201773545567/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (55826565201773545567/50000000000000000000 : ℝ) ≤ (10268755454104379/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (55826565201773545567/50000000000000000000 : ℝ)^32 ≤ (10268755454104379/10000000000000000 : ℝ)^133 := by
      have hnat : (55826565201773545567 : ℕ)^32*10000000000000000^133 ≤ 10268755454104379^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55826565201773545567 50000000000000000000 10268755454104379 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10268755454104379/10000000000000000 : ℝ)) (X := (55826565201773545567/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (30826565201773545567/25000000000000000000 : ℝ) ≤ (10516982679307971/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (30826565201773545567/25000000000000000000 : ℝ)^32 ≤ (10516982679307971/10000000000000000 : ℝ)^133 := by
      have hnat : (30826565201773545567 : ℕ)^32*10000000000000000^133 ≤ 10516982679307971^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30826565201773545567 25000000000000000000 10516982679307971 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10516982679307971/10000000000000000 : ℝ)) (X := (30826565201773545567/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(268755454104379/5961900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(31028403150449/745237500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (59619/100000 : ℝ)) (alpha := (268755454104379/5961900000000000 : ℝ)) (beta := (31028403150449/745237500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (59619/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(268755454104379/5961900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(31028403150449/745237500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (12271/100000 : ℝ) ^ (133/32 : ℝ) ≤ (8168218035258229/50000000000000000000 : ℝ) := by
    have hpowers : (12271/100000 : ℝ)^133 ≤ (8168218035258229/50000000000000000000 : ℝ)^32 := by
      have hnat : (12271 : ℕ)^133*50000000000000000000^32 ≤ 8168218035258229^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12271 100000 8168218035258229 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12271/100000 : ℝ)) (X := (8168218035258229/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (50008168218035258229/50000000000000000000 : ℝ) ≤ (10000393032729733/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50008168218035258229/50000000000000000000 : ℝ)^32 ≤ (10000393032729733/10000000000000000 : ℝ)^133 := by
      have hnat : (50008168218035258229 : ℕ)^32*10000000000000000^133 ≤ 10000393032729733^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008168218035258229 50000000000000000000 10000393032729733 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000393032729733/10000000000000000 : ℝ)) (X := (50008168218035258229/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (25008168218035258229/25000000000000000000 : ℝ) ≤ (5000393008355671/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25008168218035258229/25000000000000000000 : ℝ)^32 ≤ (5000393008355671/5000000000000000 : ℝ)^133 := by
      have hnat : (25008168218035258229 : ℕ)^32*5000000000000000^133 ≤ 5000393008355671^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008168218035258229 25000000000000000000 5000393008355671 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000393008355671/5000000000000000 : ℝ)) (X := (25008168218035258229/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(56147532819/175300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(392983981609/1227100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (12271/100000 : ℝ)) (alpha := (56147532819/175300000000000 : ℝ)) (beta := (392983981609/1227100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (12271/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(56147532819/175300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(392983981609/1227100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-3546261343/10000000000 : ℝ)*X 0 0+(3546210573/10000000000 : ℝ)*X 0 1+(5789014399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((3546227583/10000000000 : ℝ)*X 1 0+(-3546176813/10000000000 : ℝ)*X 1 1+(5789072297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((2790210739/5000000000 : ℝ)*X 2 0+(2790235837/5000000000 : ℝ)*X 2 1+(-265795591/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((44921079/100000000 : ℝ)*X 0 0+(4492148307/10000000000 : ℝ)*X 0 1+(250622693/625000000 : ℝ)*X 0 2+(44921079/100000000 : ℝ)*X 1 0+(4492148307/10000000000 : ℝ)*X 1 1+(250622693/625000000 : ℝ)*X 1 2+(44921079/100000000 : ℝ)*X 2 0+(4492148307/10000000000 : ℝ)*X 2 1+(250622693/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-3518376371/10000000000 : ℝ)*X 0 0+(1706779919/5000000000 : ℝ)*X 0 1+(5925466901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((351833441/1000000000 : ℝ)*X 1 0+(-3413519127/10000000000 : ℝ)*X 1 1+(237021471/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((2753253327/5000000000 : ℝ)*X 2 0+(5738161799/10000000000 : ℝ)*X 2 1+(-47761573/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_12 : ((4528779393/10000000000 : ℝ)*X 0 0+(471930219/1000000000 : ℝ)*X 0 1+(373159471/1000000000 : ℝ)*X 0 2+(4528779393/10000000000 : ℝ)*X 1 0+(471930219/1000000000 : ℝ)*X 1 1+(373159471/1000000000 : ℝ)*X 1 2+(4528779393/10000000000 : ℝ)*X 2 0+(471930219/1000000000 : ℝ)*X 2 1+(373159471/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((-136544061/400000000 : ℝ)*X 0 0+(1759167877/5000000000 : ℝ)*X 0 1+(2962733163/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((1706779993/5000000000 : ℝ)*X 1 0+(-3518292941/10000000000 : ℝ)*X 1 1+(5925537621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((5738101517/10000000000 : ℝ)*X 2 0+(5506567691/10000000000 : ℝ)*X 2 1+(-1194039371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_18 : ((471925257/1000000000 : ℝ)*X 0 0+(4528829553/10000000000 : ℝ)*X 0 1+(1865797411/5000000000 : ℝ)*X 0 2+(471925257/1000000000 : ℝ)*X 1 0+(4528829553/10000000000 : ℝ)*X 1 1+(1865797411/5000000000 : ℝ)*X 1 2+(471925257/1000000000 : ℝ)*X 2 0+(4528829553/10000000000 : ℝ)*X 2 1+(1865797411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_19 : ((-712594877/2000000000 : ℝ)*X 0 0+(353102147/1000000000 : ℝ)*X 0 1+(578768819/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((3531023091/10000000000 : ℝ)*X 1 0+(-1781445741/5000000000 : ℝ)*X 1 1+(5787757999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((1118107381/2000000000 : ℝ)*X 2 0+(1392799451/2500000000 : ℝ)*X 2 1+(-1327649463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_25 : ((1118431451/2500000000 : ℝ)*X 0 0+(141053401/312500000 : ℝ)*X 0 1+(2003319933/5000000000 : ℝ)*X 0 2+(1118431451/2500000000 : ℝ)*X 1 0+(141053401/312500000 : ℝ)*X 1 1+(2003319933/5000000000 : ℝ)*X 1 2+(1118431451/2500000000 : ℝ)*X 2 0+(141053401/312500000 : ℝ)*X 2 1+(2003319933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s4_s4_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((21469/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21469/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (124475440328349442555278149/19091390526250000000000000000000 : ℝ) := by norm_num
    linear_combination (4801/7812500000 : ℝ)*(base50) + (12634529568209/1000000000000 : ℝ)*(base59) + (1237403025527/200000000000 : ℝ)*(base60) + (13920404602639/500000000000 : ℝ)*(major_s4_0) + (13920404602639/500000000000 : ℝ)*(major_s4_1) + (13920404602639/500000000000 : ℝ)*(major_s4_2) + (1472011/62500000000 : ℝ)*(sp_s4_0) + (125287643/500000000000 : ℝ)*(sp_s4_2) + (468454439543/12500000000 : ℝ)*(sp_s4_7) + (9369110443147/250000000000 : ℝ)*(sp_s4_8) + (37476191197301/1000000000000 : ℝ)*(sp_s4_9) + (18205078726451/1000000000000 : ℝ)*(sp_s4_12) + (15764243/250000000000 : ℝ)*(sp_s4_13) + (11967273/125000000000 : ℝ)*(sp_s4_25) + (4551293616159/250000000000 : ℝ)*(f.failure) + (9369110443147/250000000000 : ℝ)*(f.sum) + (244544290515230837/307388550000000000000000000000 : ℝ)*base63 + (153692645401779/613550000000000000000000000 : ℝ)*base65 + (7172909856743/87675000000000000000000000 : ℝ)*base66 + (9051666078881/21912500000000000000000000 : ℝ)*base69 + (18583145791737243967/36582305200000000000000000000000 : ℝ)*base71 + (4567143546339/119248000000000000000000000 : ℝ)*base73 + (67173239692729/87675000000000000000000000 : ℝ)*base75 + (1959982647083841/2981200000000000000000000000 : ℝ)*base77 + (522335497777338361/10455068400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (847/1562500000000000 : ℝ)*base87 + (847/1562500000000000 : ℝ)*base89 + (847/1562500000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21469/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21469/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1167763609319549615422003587813/103857164462800000000000000000000000 : ℝ) := by norm_num
    linear_combination (5868799/1000000000000 : ℝ)*(base40) + (6317347899427/500000000000 : ℝ)*(base59) + (805960077771/125000000000 : ℝ)*(base60) + (27841220208171/1000000000000 : ℝ)*(major_s4_0) + (27841220208171/1000000000000 : ℝ)*(major_s4_1) + (27841220208171/1000000000000 : ℝ)*(major_s4_2) + (420888411/500000000000 : ℝ)*(sp_s4_1) + (52183443/250000000000 : ℝ)*(sp_s4_6) + (257485357/250000000000 : ℝ)*(sp_s4_8) + (9369248361977/250000000000 : ℝ)*(sp_s4_13) + (18737560864829/500000000000 : ℝ)*(sp_s4_14) + (9369023224093/250000000000 : ℝ)*(sp_s4_15) + (18205234486679/1000000000000 : ℝ)*(sp_s4_18) + (56284471/62500000000 : ℝ)*(sp_s4_21) + (18205443220451/1000000000000 : ℝ)*(f.failure) + (9369248361977/250000000000 : ℝ)*(f.sum) + (797688531429699709/1741868450000000000000000000000 : ℝ)*base62 + (75431932830469/1227100000000000000000000000 : ℝ)*base64 + (150719517719779/496825000000000000000000000 : ℝ)*base66 + (124698623553769/175300000000000000000000000 : ℝ)*base68 + (30046257784889718683/73164610400000000000000000000000 : ℝ)*base71 + (607288049715749/1192480000000000000000000000 : ℝ)*base72 + (569072804189217/1987300000000000000000000000 : ℝ)*base74 + (483001149580451/5962400000000000000000000000 : ℝ)*base76 + (29280326752144062489/118490775200000000000000000000000 : ℝ)*base78 + (477/1562500000000000 : ℝ)*base87 + (477/1562500000000000 : ℝ)*base89 + (477/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(243/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(243/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (50082680267338344870417423/3709184445100000000000000000000 : ℝ) := by norm_num
    linear_combination (3120919/1000000000000 : ℝ)*(base40) + (1557129/500000000000 : ℝ)*(base50) + (494359211147/500000000000 : ℝ)*(base59) + (53918503369/12500000000 : ℝ)*(major_s4_0) + (53918503369/12500000000 : ℝ)*(major_s4_1) + (53918503369/12500000000 : ℝ)*(major_s4_2) + (107894563/1000000000000 : ℝ)*(sp_s4_0) + (175043059/500000000000 : ℝ)*(sp_s4_12) + (226848621/1000000000000 : ℝ)*(sp_s4_15) + (14697377/1000000000000 : ℝ)*(sp_s4_18) + (5806252654623/1000000000000 : ℝ)*(sp_s4_19) + (2903180274593/500000000000 : ℝ)*(sp_s4_20) + (2903066850283/500000000000 : ℝ)*(sp_s4_21) + (2820230705571/1000000000000 : ℝ)*(sp_s4_25) + (2820595489067/1000000000000 : ℝ)*(f.failure) + (2903180274593/500000000000 : ℝ)*(f.sum) + (5714964694727567/130640133750000000000000000000 : ℝ)*base62 + (5625286135271/12271000000000000000000000 : ℝ)*base65 + (474486868261211/596190000000000000000000000 : ℝ)*base67 + (900615338299/1753000000000000000000000 : ℝ)*base69 + (19235877973582787/457278815000000000000000000000 : ℝ)*base71 + (48848588831583/74530000000000000000000000 : ℝ)*base73 + (158840767760257/596190000000000000000000000 : ℝ)*base74 + (8357057484013/74530000000000000000000000 : ℝ)*base76 + (338951243582175347/444340407000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (1193/3125000000000000 : ℝ)*base87 + (1193/3125000000000000 : ℝ)*base89 + (1193/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((7453/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7453/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59619/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12271/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(12271/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21469/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21469/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21469/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21469/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(243/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(243/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305057_s4 p hpa hpb X hX hprev3

#print axioms solution
