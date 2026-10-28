-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301031_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:23:53.847848+00:00
-- url     : https://prove2.me/submissions/1e4342c0-f976-4d51-bf3b-19b6aacd47eb

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
theorem collision_support_c301031_s2_s2_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1522203091/2500000000 : ℝ)*x 0 + (-393984127/5000000000 : ℝ)*x 1 + (2728667621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1522203091/2500000000 : ℝ)^65 ≤ (1294541252537/2500000000000 : ℝ)^49 := by
    have hnat : (1522203091 : ℕ)^65*2500000000000^49 ≤ 1294541252537^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522203091 2500000000 1294541252537 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393984127/5000000000 : ℝ)^65 ≤ (343704357199/10000000000000 : ℝ)^49 := by
    have hnat : (393984127 : ℕ)^65*10000000000000^49 ≤ 343704357199^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393984127 5000000000 343704357199 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728667621/5000000000 : ℝ)^65 ≤ (1791252252709/4000000000000 : ℝ)^49 := by
    have hnat : (2728667621 : ℕ)^65*4000000000000^49 ≤ 1791252252709^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728667621 5000000000 1791252252709 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1522203091/2500000000 : ℝ), (-393984127/5000000000 : ℝ), (2728667621/5000000000 : ℝ)] ![(1294541252537/2500000000000 : ℝ), (343704357199/10000000000000 : ℝ), (1791252252709/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1522203091/2500000000 : ℝ)|^65 ≤ (1294541252537/2500000000000 : ℝ)^49
        have hw : |(1522203091/2500000000 : ℝ)|=(1522203091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393984127/5000000000 : ℝ)|^65 ≤ (343704357199/10000000000000 : ℝ)^49
        have hw : |(-393984127/5000000000 : ℝ)|=(393984127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728667621/5000000000 : ℝ)|^65 ≤ (1791252252709/4000000000000 : ℝ)^49
        have hw : |(2728667621/5000000000 : ℝ)|=(2728667621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3228240279/10000000000 : ℝ)*x 0 + (303243621/500000000 : ℝ)*x 1 + (-3640274533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3228240279/10000000000 : ℝ)^65 ≤ (22316607280293/100000000000000 : ℝ)^49 := by
    have hnat : (3228240279 : ℕ)^65*100000000000000^49 ≤ 22316607280293^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3228240279 10000000000 22316607280293 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303243621/500000000 : ℝ)^65 ≤ (3219484315449/6250000000000 : ℝ)^49 := by
    have hnat : (303243621 : ℕ)^65*6250000000000^49 ≤ 3219484315449^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303243621 500000000 3219484315449 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3640274533/10000000000 : ℝ)^65 ≤ (817863864503/3125000000000 : ℝ)^49 := by
    have hnat : (3640274533 : ℕ)^65*3125000000000^49 ≤ 817863864503^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3640274533 10000000000 817863864503 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3228240279/10000000000 : ℝ), (303243621/500000000 : ℝ), (-3640274533/10000000000 : ℝ)] ![(22316607280293/100000000000000 : ℝ), (3219484315449/6250000000000 : ℝ), (817863864503/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3228240279/10000000000 : ℝ)|^65 ≤ (22316607280293/100000000000000 : ℝ)^49
        have hw : |(3228240279/10000000000 : ℝ)|=(3228240279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303243621/500000000 : ℝ)|^65 ≤ (3219484315449/6250000000000 : ℝ)^49
        have hw : |(303243621/500000000 : ℝ)|=(303243621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3640274533/10000000000 : ℝ)|^65 ≤ (817863864503/3125000000000 : ℝ)^49
        have hw : |(-3640274533/10000000000 : ℝ)|=(3640274533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2142845193/5000000000 : ℝ)*x 0 + (4954910513/10000000000 : ℝ)*x 1 + (3841216937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142845193/5000000000 : ℝ)^65 ≤ (507790232711/1562500000000 : ℝ)^49 := by
    have hnat : (2142845193 : ℕ)^65*1562500000000^49 ≤ 507790232711^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142845193 5000000000 507790232711 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4954910513/10000000000 : ℝ)^65 ≤ (9849080388449/25000000000000 : ℝ)^49 := by
    have hnat : (4954910513 : ℕ)^65*25000000000000^49 ≤ 9849080388449^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4954910513 10000000000 9849080388449 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3841216937/10000000000 : ℝ)^65 ≤ (7026275882771/25000000000000 : ℝ)^49 := by
    have hnat : (3841216937 : ℕ)^65*25000000000000^49 ≤ 7026275882771^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841216937 10000000000 7026275882771 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142845193/5000000000 : ℝ), (4954910513/10000000000 : ℝ), (3841216937/10000000000 : ℝ)] ![(507790232711/1562500000000 : ℝ), (9849080388449/25000000000000 : ℝ), (7026275882771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142845193/5000000000 : ℝ)|^65 ≤ (507790232711/1562500000000 : ℝ)^49
        have hw : |(2142845193/5000000000 : ℝ)|=(2142845193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4954910513/10000000000 : ℝ)|^65 ≤ (9849080388449/25000000000000 : ℝ)^49
        have hw : |(4954910513/10000000000 : ℝ)|=(4954910513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3841216937/10000000000 : ℝ)|^65 ≤ (7026275882771/25000000000000 : ℝ)^49
        have hw : |(3841216937/10000000000 : ℝ)|=(3841216937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-352680793/1000000000 : ℝ)*x 0 + (1101915083/2000000000 : ℝ)*x 1 + (1994790861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352680793/1000000000 : ℝ)^65 ≤ (25095052783403/100000000000000 : ℝ)^49 := by
    have hnat : (352680793 : ℕ)^65*100000000000000^49 ≤ 25095052783403^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352680793 1000000000 25095052783403 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101915083/2000000000 : ℝ)^65 ≤ (362806671243/800000000000 : ℝ)^49 := by
    have hnat : (1101915083 : ℕ)^65*800000000000^49 ≤ 362806671243^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101915083 2000000000 362806671243 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994790861/5000000000 : ℝ)^65 ≤ (29554113295783/100000000000000 : ℝ)^49 := by
    have hnat : (1994790861 : ℕ)^65*100000000000000^49 ≤ 29554113295783^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994790861 5000000000 29554113295783 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352680793/1000000000 : ℝ), (1101915083/2000000000 : ℝ), (1994790861/5000000000 : ℝ)] ![(25095052783403/100000000000000 : ℝ), (362806671243/800000000000 : ℝ), (29554113295783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352680793/1000000000 : ℝ)|^65 ≤ (25095052783403/100000000000000 : ℝ)^49
        have hw : |(-352680793/1000000000 : ℝ)|=(352680793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101915083/2000000000 : ℝ)|^65 ≤ (362806671243/800000000000 : ℝ)^49
        have hw : |(1101915083/2000000000 : ℝ)|=(1101915083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1994790861/5000000000 : ℝ)|^65 ≤ (29554113295783/100000000000000 : ℝ)^49
        have hw : |(1994790861/5000000000 : ℝ)|=(1994790861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5851187209/10000000000 : ℝ)*x 0 + (-21430843/10000000000 : ℝ)*x 1 + (240252607/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5851187209/10000000000 : ℝ)^65 ≤ (49118153538033/100000000000000 : ℝ)^49 := by
    have hnat : (5851187209 : ℕ)^65*100000000000000^49 ≤ 49118153538033^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5851187209 10000000000 49118153538033 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21430843/10000000000 : ℝ)^65 ≤ (14404953903/50000000000000 : ℝ)^49 := by
    have hnat : (21430843 : ℕ)^65*50000000000000^49 ≤ 14404953903^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21430843 10000000000 14404953903 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240252607/400000000 : ℝ)^65 ≤ (2542651827243/5000000000000 : ℝ)^49 := by
    have hnat : (240252607 : ℕ)^65*5000000000000^49 ≤ 2542651827243^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240252607 400000000 2542651827243 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5851187209/10000000000 : ℝ), (-21430843/10000000000 : ℝ), (240252607/400000000 : ℝ)] ![(49118153538033/100000000000000 : ℝ), (14404953903/50000000000000 : ℝ), (2542651827243/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5851187209/10000000000 : ℝ)|^65 ≤ (49118153538033/100000000000000 : ℝ)^49
        have hw : |(5851187209/10000000000 : ℝ)|=(5851187209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21430843/10000000000 : ℝ)|^65 ≤ (14404953903/50000000000000 : ℝ)^49
        have hw : |(-21430843/10000000000 : ℝ)|=(21430843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240252607/400000000 : ℝ)|^65 ≤ (2542651827243/5000000000000 : ℝ)^49
        have hw : |(240252607/400000000 : ℝ)|=(240252607/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1365462573/5000000000 : ℝ)*x 0 + (1379104059/2000000000 : ℝ)*x 1 + (-1544633173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1365462573/5000000000 : ℝ)^65 ≤ (17875067443749/100000000000000 : ℝ)^49 := by
    have hnat : (1365462573 : ℕ)^65*100000000000000^49 ≤ 17875067443749^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365462573 5000000000 17875067443749 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379104059/2000000000 : ℝ)^65 ≤ (3817106308399/6250000000000 : ℝ)^49 := by
    have hnat : (1379104059 : ℕ)^65*6250000000000^49 ≤ 3817106308399^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379104059 2000000000 3817106308399 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1544633173/5000000000 : ℝ)^65 ≤ (10525615805289/50000000000000 : ℝ)^49 := by
    have hnat : (1544633173 : ℕ)^65*50000000000000^49 ≤ 10525615805289^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544633173 5000000000 10525615805289 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1365462573/5000000000 : ℝ), (1379104059/2000000000 : ℝ), (-1544633173/5000000000 : ℝ)] ![(17875067443749/100000000000000 : ℝ), (3817106308399/6250000000000 : ℝ), (10525615805289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1365462573/5000000000 : ℝ)|^65 ≤ (17875067443749/100000000000000 : ℝ)^49
        have hw : |(1365462573/5000000000 : ℝ)|=(1365462573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379104059/2000000000 : ℝ)|^65 ≤ (3817106308399/6250000000000 : ℝ)^49
        have hw : |(1379104059/2000000000 : ℝ)|=(1379104059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1544633173/5000000000 : ℝ)|^65 ≤ (10525615805289/50000000000000 : ℝ)^49
        have hw : |(-1544633173/5000000000 : ℝ)|=(1544633173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_12 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1927774857/5000000000 : ℝ)*x 0 + (655961999/1250000000 : ℝ)*x 1 + (1978884449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1927774857/5000000000 : ℝ)^65 ≤ (7061075001937/25000000000000 : ℝ)^49 := by
    have hnat : (1927774857 : ℕ)^65*25000000000000^49 ≤ 7061075001937^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927774857 5000000000 7061075001937 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655961999/1250000000 : ℝ)^65 ≤ (42513794141093/100000000000000 : ℝ)^49 := by
    have hnat : (655961999 : ℕ)^65*100000000000000^49 ≤ 42513794141093^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655961999 1250000000 42513794141093 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978884449/5000000000 : ℝ)^65 ≤ (29241905828529/100000000000000 : ℝ)^49 := by
    have hnat : (1978884449 : ℕ)^65*100000000000000^49 ≤ 29241905828529^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978884449 5000000000 29241905828529 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1927774857/5000000000 : ℝ), (655961999/1250000000 : ℝ), (1978884449/5000000000 : ℝ)] ![(7061075001937/25000000000000 : ℝ), (42513794141093/100000000000000 : ℝ), (29241905828529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1927774857/5000000000 : ℝ)|^65 ≤ (7061075001937/25000000000000 : ℝ)^49
        have hw : |(1927774857/5000000000 : ℝ)|=(1927774857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655961999/1250000000 : ℝ)|^65 ≤ (42513794141093/100000000000000 : ℝ)^49
        have hw : |(655961999/1250000000 : ℝ)|=(655961999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1978884449/5000000000 : ℝ)|^65 ≤ (29241905828529/100000000000000 : ℝ)^49
        have hw : |(1978884449/5000000000 : ℝ)|=(1978884449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3637970059/10000000000 : ℝ)*x 0 + (1177015167/2500000000 : ℝ)*x 1 + (4729447253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3637970059/10000000000 : ℝ)^65 ≤ (26149668048221/100000000000000 : ℝ)^49 := by
    have hnat : (3637970059 : ℕ)^65*100000000000000^49 ≤ 26149668048221^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3637970059 10000000000 26149668048221 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177015167/2500000000 : ℝ)^65 ≤ (18407082944831/50000000000000 : ℝ)^49 := by
    have hnat : (1177015167 : ℕ)^65*50000000000000^49 ≤ 18407082944831^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177015167 2500000000 18407082944831 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4729447253/10000000000 : ℝ)^65 ≤ (9259041511021/25000000000000 : ℝ)^49 := by
    have hnat : (4729447253 : ℕ)^65*25000000000000^49 ≤ 9259041511021^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4729447253 10000000000 9259041511021 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3637970059/10000000000 : ℝ), (1177015167/2500000000 : ℝ), (4729447253/10000000000 : ℝ)] ![(26149668048221/100000000000000 : ℝ), (18407082944831/50000000000000 : ℝ), (9259041511021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3637970059/10000000000 : ℝ)|^65 ≤ (26149668048221/100000000000000 : ℝ)^49
        have hw : |(-3637970059/10000000000 : ℝ)|=(3637970059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1177015167/2500000000 : ℝ)|^65 ≤ (18407082944831/50000000000000 : ℝ)^49
        have hw : |(1177015167/2500000000 : ℝ)|=(1177015167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4729447253/10000000000 : ℝ)|^65 ≤ (9259041511021/25000000000000 : ℝ)^49
        have hw : |(4729447253/10000000000 : ℝ)|=(4729447253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3711920059/5000000000 : ℝ)*x 0 + (-289168751/5000000000 : ℝ)*x 1 + (508944579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3711920059/5000000000 : ℝ)^65 ≤ (33678667126271/50000000000000 : ℝ)^49 := by
    have hnat : (3711920059 : ℕ)^65*50000000000000^49 ≤ 33678667126271^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711920059 5000000000 33678667126271 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289168751/5000000000 : ℝ)^65 ≤ (1140159680833/50000000000000 : ℝ)^49 := by
    have hnat : (289168751 : ℕ)^65*50000000000000^49 ≤ 1140159680833^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289168751 5000000000 1140159680833 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508944579/1250000000 : ℝ)^65 ≤ (30362346375191/100000000000000 : ℝ)^49 := by
    have hnat : (508944579 : ℕ)^65*100000000000000^49 ≤ 30362346375191^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508944579 1250000000 30362346375191 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3711920059/5000000000 : ℝ), (-289168751/5000000000 : ℝ), (508944579/1250000000 : ℝ)] ![(33678667126271/50000000000000 : ℝ), (1140159680833/50000000000000 : ℝ), (30362346375191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3711920059/5000000000 : ℝ)|^65 ≤ (33678667126271/50000000000000 : ℝ)^49
        have hw : |(3711920059/5000000000 : ℝ)|=(3711920059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-289168751/5000000000 : ℝ)|^65 ≤ (1140159680833/50000000000000 : ℝ)^49
        have hw : |(-289168751/5000000000 : ℝ)|=(289168751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508944579/1250000000 : ℝ)|^65 ≤ (30362346375191/100000000000000 : ℝ)^49
        have hw : |(508944579/1250000000 : ℝ)|=(508944579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1306969093/5000000000 : ℝ)*x 0 + (6488852791/10000000000 : ℝ)*x 1 + (-741009349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306969093/5000000000 : ℝ)^65 ≤ (16866477648043/100000000000000 : ℝ)^49 := by
    have hnat : (1306969093 : ℕ)^65*100000000000000^49 ≤ 16866477648043^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306969093 5000000000 16866477648043 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6488852791/10000000000 : ℝ)^65 ≤ (11268471063573/20000000000000 : ℝ)^49 := by
    have hnat : (6488852791 : ℕ)^65*20000000000000^49 ≤ 11268471063573^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6488852791 10000000000 11268471063573 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (741009349/2000000000 : ℝ)^65 ≤ (26791167017339/100000000000000 : ℝ)^49 := by
    have hnat : (741009349 : ℕ)^65*100000000000000^49 ≤ 26791167017339^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741009349 2000000000 26791167017339 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306969093/5000000000 : ℝ), (6488852791/10000000000 : ℝ), (-741009349/2000000000 : ℝ)] ![(16866477648043/100000000000000 : ℝ), (11268471063573/20000000000000 : ℝ), (26791167017339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306969093/5000000000 : ℝ)|^65 ≤ (16866477648043/100000000000000 : ℝ)^49
        have hw : |(1306969093/5000000000 : ℝ)|=(1306969093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6488852791/10000000000 : ℝ)|^65 ≤ (11268471063573/20000000000000 : ℝ)^49
        have hw : |(6488852791/10000000000 : ℝ)|=(6488852791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-741009349/2000000000 : ℝ)|^65 ≤ (26791167017339/100000000000000 : ℝ)^49
        have hw : |(-741009349/2000000000 : ℝ)|=(741009349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (700280141/2500000000 : ℝ)*x 0 + (2537349513/5000000000 : ℝ)*x 1 + (15912343/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (700280141/2500000000 : ℝ)^65 ≤ (577721777/3125000000 : ℝ)^49 := by
    have hnat : (700280141 : ℕ)^65*3125000000^49 ≤ 577721777^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700280141 2500000000 577721777 3125000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537349513/5000000000 : ℝ)^65 ≤ (20332357434851/50000000000000 : ℝ)^49 := by
    have hnat : (2537349513 : ℕ)^65*50000000000000^49 ≤ 20332357434851^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537349513 5000000000 20332357434851 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15912343/31250000 : ℝ)^65 ≤ (5106023532113/12500000000000 : ℝ)^49 := by
    have hnat : (15912343 : ℕ)^65*12500000000000^49 ≤ 5106023532113^49*31250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15912343 31250000 5106023532113 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(700280141/2500000000 : ℝ), (2537349513/5000000000 : ℝ), (15912343/31250000 : ℝ)] ![(577721777/3125000000 : ℝ), (20332357434851/50000000000000 : ℝ), (5106023532113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(700280141/2500000000 : ℝ)|^65 ≤ (577721777/3125000000 : ℝ)^49
        have hw : |(700280141/2500000000 : ℝ)|=(700280141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537349513/5000000000 : ℝ)|^65 ≤ (20332357434851/50000000000000 : ℝ)^49
        have hw : |(2537349513/5000000000 : ℝ)|=(2537349513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15912343/31250000 : ℝ)|^65 ≤ (5106023532113/12500000000000 : ℝ)^49
        have hw : |(15912343/31250000 : ℝ)|=(15912343/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-725350537/2500000000 : ℝ)*x 0 + (2988667473/5000000000 : ℝ)*x 1 + (1011303609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (725350537/2500000000 : ℝ)^65 ≤ (387402984097/2000000000000 : ℝ)^49 := by
    have hnat : (725350537 : ℕ)^65*2000000000000^49 ≤ 387402984097^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725350537 2500000000 387402984097 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2988667473/5000000000 : ℝ)^65 ≤ (12631952639279/25000000000000 : ℝ)^49 := by
    have hnat : (2988667473 : ℕ)^65*25000000000000^49 ≤ 12631952639279^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988667473 5000000000 12631952639279 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011303609/2500000000 : ℝ)^65 ≤ (30102040212861/100000000000000 : ℝ)^49 := by
    have hnat : (1011303609 : ℕ)^65*100000000000000^49 ≤ 30102040212861^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011303609 2500000000 30102040212861 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-725350537/2500000000 : ℝ), (2988667473/5000000000 : ℝ), (1011303609/2500000000 : ℝ)] ![(387402984097/2000000000000 : ℝ), (12631952639279/25000000000000 : ℝ), (30102040212861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-725350537/2500000000 : ℝ)|^65 ≤ (387402984097/2000000000000 : ℝ)^49
        have hw : |(-725350537/2500000000 : ℝ)|=(725350537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2988667473/5000000000 : ℝ)|^65 ≤ (12631952639279/25000000000000 : ℝ)^49
        have hw : |(2988667473/5000000000 : ℝ)|=(2988667473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011303609/2500000000 : ℝ)|^65 ≤ (30102040212861/100000000000000 : ℝ)^49
        have hw : |(1011303609/2500000000 : ℝ)|=(1011303609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7082380629/10000000000 : ℝ)*x 0 + (-7909621/1250000000 : ℝ)*x 1 + (1171851239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7082380629/10000000000 : ℝ)^65 ≤ (31639397944097/50000000000000 : ℝ)^49 := by
    have hnat : (7082380629 : ℕ)^65*50000000000000^49 ≤ 31639397944097^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7082380629 10000000000 31639397944097 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7909621/1250000000 : ℝ)^65 ≤ (30284825069/25000000000000 : ℝ)^49 := by
    have hnat : (7909621 : ℕ)^65*25000000000000^49 ≤ 30284825069^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7909621 1250000000 30284825069 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171851239/2500000000 : ℝ)^65 ≤ (7320012961833/20000000000000 : ℝ)^49 := by
    have hnat : (1171851239 : ℕ)^65*20000000000000^49 ≤ 7320012961833^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171851239 2500000000 7320012961833 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7082380629/10000000000 : ℝ), (-7909621/1250000000 : ℝ), (1171851239/2500000000 : ℝ)] ![(31639397944097/50000000000000 : ℝ), (30284825069/25000000000000 : ℝ), (7320012961833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7082380629/10000000000 : ℝ)|^65 ≤ (31639397944097/50000000000000 : ℝ)^49
        have hw : |(7082380629/10000000000 : ℝ)|=(7082380629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7909621/1250000000 : ℝ)|^65 ≤ (30284825069/25000000000000 : ℝ)^49
        have hw : |(-7909621/1250000000 : ℝ)|=(7909621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1171851239/2500000000 : ℝ)|^65 ≤ (7320012961833/20000000000000 : ℝ)^49
        have hw : |(1171851239/2500000000 : ℝ)|=(1171851239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (76396607/312500000 : ℝ)*x 0 + (3426837307/5000000000 : ℝ)*x 1 + (-3408455821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76396607/312500000 : ℝ)^65 ≤ (7716679759911/50000000000000 : ℝ)^49 := by
    have hnat : (76396607 : ℕ)^65*50000000000000^49 ≤ 7716679759911^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76396607 312500000 7716679759911 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3426837307/5000000000 : ℝ)^65 ≤ (1211650795371/2000000000000 : ℝ)^49 := by
    have hnat : (3426837307 : ℕ)^65*2000000000000^49 ≤ 1211650795371^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3426837307 5000000000 1211650795371 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3408455821/10000000000 : ℝ)^65 ≤ (239841006903/1000000000000 : ℝ)^49 := by
    have hnat : (3408455821 : ℕ)^65*1000000000000^49 ≤ 239841006903^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408455821 10000000000 239841006903 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(76396607/312500000 : ℝ), (3426837307/5000000000 : ℝ), (-3408455821/10000000000 : ℝ)] ![(7716679759911/50000000000000 : ℝ), (1211650795371/2000000000000 : ℝ), (239841006903/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(76396607/312500000 : ℝ)|^65 ≤ (7716679759911/50000000000000 : ℝ)^49
        have hw : |(76396607/312500000 : ℝ)|=(76396607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3426837307/5000000000 : ℝ)|^65 ≤ (1211650795371/2000000000000 : ℝ)^49
        have hw : |(3426837307/5000000000 : ℝ)|=(3426837307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3408455821/10000000000 : ℝ)|^65 ≤ (239841006903/1000000000000 : ℝ)^49
        have hw : |(-3408455821/10000000000 : ℝ)|=(3408455821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301031_s2_s2_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5243881733/10000000000 : ℝ)*x 0 + (2165799519/5000000000 : ℝ)*x 1 + (1735306143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243881733/10000000000 : ℝ)^65 ≤ (21236403996481/50000000000000 : ℝ)^49 := by
    have hnat : (5243881733 : ℕ)^65*50000000000000^49 ≤ 21236403996481^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243881733 10000000000 21236403996481 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2165799519/5000000000 : ℝ)^65 ≤ (1648059105611/5000000000000 : ℝ)^49 := by
    have hnat : (2165799519 : ℕ)^65*5000000000000^49 ≤ 1648059105611^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165799519 5000000000 1648059105611 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1735306143/5000000000 : ℝ)^65 ≤ (12283004942259/50000000000000 : ℝ)^49 := by
    have hnat : (1735306143 : ℕ)^65*50000000000000^49 ≤ 12283004942259^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735306143 5000000000 12283004942259 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243881733/10000000000 : ℝ), (2165799519/5000000000 : ℝ), (1735306143/5000000000 : ℝ)] ![(21236403996481/50000000000000 : ℝ), (1648059105611/5000000000000 : ℝ), (12283004942259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243881733/10000000000 : ℝ)|^65 ≤ (21236403996481/50000000000000 : ℝ)^49
        have hw : |(5243881733/10000000000 : ℝ)|=(5243881733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2165799519/5000000000 : ℝ)|^65 ≤ (1648059105611/5000000000000 : ℝ)^49
        have hw : |(2165799519/5000000000 : ℝ)|=(2165799519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1735306143/5000000000 : ℝ)|^65 ≤ (12283004942259/50000000000000 : ℝ)^49
        have hw : |(1735306143/5000000000 : ℝ)|=(1735306143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301031_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((13603/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13603/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(43967/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(43967/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19497/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19497/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1389/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1389/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6199/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(6199/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41829/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41829/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (13603/20000 : ℝ) ^ (129/32 : ℝ) ≤ (10572013544560136959/50000000000000000000 : ℝ) := by
    have hpowers : (13603/20000 : ℝ)^129 ≤ (10572013544560136959/50000000000000000000 : ℝ)^32 := by
      have hnat : (13603 : ℕ)^129*50000000000000000000^32 ≤ 10572013544560136959^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13603 20000 10572013544560136959 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13603/20000 : ℝ)) (X := (10572013544560136959/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (60572013544560136959/50000000000000000000 : ℝ) ≤ (10487308982883021/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (60572013544560136959/50000000000000000000 : ℝ)^32 ≤ (10487308982883021/10000000000000000 : ℝ)^129 := by
      have hnat : (60572013544560136959 : ℕ)^32*10000000000000000^129 ≤ 10487308982883021^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60572013544560136959 50000000000000000000 10487308982883021 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10487308982883021/10000000000000000 : ℝ)) (X := (60572013544560136959/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (35572013544560136959/25000000000000000000 : ℝ) ≤ (10914284544680353/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (35572013544560136959/25000000000000000000 : ℝ)^32 ≤ (10914284544680353/10000000000000000 : ℝ)^129 := by
      have hnat : (35572013544560136959 : ℕ)^32*10000000000000000^129 ≤ 10914284544680353^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35572013544560136959 25000000000000000000 10914284544680353 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10914284544680353/10000000000000000 : ℝ)) (X := (35572013544560136959/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(487308982883021/6801500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(106743890449333/1700375000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (13603/20000 : ℝ)) (alpha := (487308982883021/6801500000000000 : ℝ)) (beta := (106743890449333/1700375000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13603/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(487308982883021/6801500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(106743890449333/1700375000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (43967/100000 : ℝ) ^ (129/32 : ℝ) ≤ (728425335864219473/20000000000000000000 : ℝ) := by
    have hpowers : (43967/100000 : ℝ)^129 ≤ (728425335864219473/20000000000000000000 : ℝ)^32 := by
      have hnat : (43967 : ℕ)^129*20000000000000000000^32 ≤ 728425335864219473^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43967 100000 728425335864219473 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43967/100000 : ℝ)) (X := (728425335864219473/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (20728425335864219473/20000000000000000000 : ℝ) ≤ (10089135849841923/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20728425335864219473/20000000000000000000 : ℝ)^32 ≤ (10089135849841923/10000000000000000 : ℝ)^129 := by
      have hnat : (20728425335864219473 : ℕ)^32*10000000000000000^129 ≤ 10089135849841923^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20728425335864219473 20000000000000000000 10089135849841923 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10089135849841923/10000000000000000 : ℝ)) (X := (20728425335864219473/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (10728425335864219473/10000000000000000000 : ℝ) ≤ (10175946558627879/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (10728425335864219473/10000000000000000000 : ℝ)^32 ≤ (10175946558627879/10000000000000000 : ℝ)^129 := by
      have hnat : (10728425335864219473 : ℕ)^32*10000000000000000^129 ≤ 10175946558627879^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10728425335864219473 10000000000000000000 10175946558627879 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10175946558627879/10000000000000000 : ℝ)) (X := (10728425335864219473/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(89135849841923/4396700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(21702677196489/1099175000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (43967/100000 : ℝ)) (alpha := (89135849841923/4396700000000000 : ℝ)) (beta := (21702677196489/1099175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (43967/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(89135849841923/4396700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(21702677196489/1099175000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (19497/25000 : ℝ) ^ (129/32 : ℝ) ≤ (18352997464717634757/50000000000000000000 : ℝ) := by
    have hpowers : (19497/25000 : ℝ)^129 ≤ (18352997464717634757/50000000000000000000 : ℝ)^32 := by
      have hnat : (19497 : ℕ)^129*50000000000000000000^32 ≤ 18352997464717634757^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19497 25000 18352997464717634757 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19497/25000 : ℝ)) (X := (18352997464717634757/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (68352997464717634757/50000000000000000000 : ℝ) ≤ (675404194067639/625000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (68352997464717634757/50000000000000000000 : ℝ)^32 ≤ (675404194067639/625000000000000 : ℝ)^129 := by
      have hnat : (68352997464717634757 : ℕ)^32*625000000000000^129 ≤ 675404194067639^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68352997464717634757 50000000000000000000 675404194067639 625000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (675404194067639/625000000000000 : ℝ)) (X := (68352997464717634757/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (43352997464717634757/25000000000000000000 : ℝ) ≤ (1432901910738711/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (43352997464717634757/25000000000000000000 : ℝ)^32 ≤ (1432901910738711/1250000000000000 : ℝ)^129 := by
      have hnat : (43352997464717634757 : ℕ)^32*1250000000000000^129 ≤ 1432901910738711^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43352997464717634757 25000000000000000000 1432901910738711 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1432901910738711/1250000000000000 : ℝ)) (X := (43352997464717634757/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(50404194067639/487425000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(82093522603433/974850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (19497/25000 : ℝ)) (alpha := (50404194067639/487425000000000 : ℝ)) (beta := (82093522603433/974850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19497/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(50404194067639/487425000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(82093522603433/974850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((1522203091/2500000000 : ℝ)*X 1 0+(-393984127/5000000000 : ℝ)*X 1 1+(2728667621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((3228240279/10000000000 : ℝ)*X 2 0+(303243621/500000000 : ℝ)*X 2 1+(-3640274533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2142845193/5000000000 : ℝ)*X 0 0+(4954910513/10000000000 : ℝ)*X 0 1+(3841216937/10000000000 : ℝ)*X 0 2+(2142845193/5000000000 : ℝ)*X 1 0+(4954910513/10000000000 : ℝ)*X 1 1+(3841216937/10000000000 : ℝ)*X 1 2+(2142845193/5000000000 : ℝ)*X 2 0+(4954910513/10000000000 : ℝ)*X 2 1+(3841216937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-352680793/1000000000 : ℝ)*X 0 0+(1101915083/2000000000 : ℝ)*X 0 1+(1994790861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5851187209/10000000000 : ℝ)*X 1 0+(-21430843/10000000000 : ℝ)*X 1 1+(240252607/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1365462573/5000000000 : ℝ)*X 2 0+(1379104059/2000000000 : ℝ)*X 2 1+(-1544633173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((1927774857/5000000000 : ℝ)*X 0 0+(655961999/1250000000 : ℝ)*X 0 1+(1978884449/5000000000 : ℝ)*X 0 2+(1927774857/5000000000 : ℝ)*X 1 0+(655961999/1250000000 : ℝ)*X 1 1+(1978884449/5000000000 : ℝ)*X 1 2+(1927774857/5000000000 : ℝ)*X 2 0+(655961999/1250000000 : ℝ)*X 2 1+(1978884449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-3637970059/10000000000 : ℝ)*X 0 0+(1177015167/2500000000 : ℝ)*X 0 1+(4729447253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((3711920059/5000000000 : ℝ)*X 1 0+(-289168751/5000000000 : ℝ)*X 1 1+(508944579/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1306969093/5000000000 : ℝ)*X 2 0+(6488852791/10000000000 : ℝ)*X 2 1+(-741009349/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((700280141/2500000000 : ℝ)*X 0 0+(2537349513/5000000000 : ℝ)*X 0 1+(15912343/31250000 : ℝ)*X 0 2+(700280141/2500000000 : ℝ)*X 1 0+(2537349513/5000000000 : ℝ)*X 1 1+(15912343/31250000 : ℝ)*X 1 2+(700280141/2500000000 : ℝ)*X 2 0+(2537349513/5000000000 : ℝ)*X 2 1+(15912343/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-725350537/2500000000 : ℝ)*X 0 0+(2988667473/5000000000 : ℝ)*X 0 1+(1011303609/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((7082380629/10000000000 : ℝ)*X 1 0+(-7909621/1250000000 : ℝ)*X 1 1+(1171851239/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((76396607/312500000 : ℝ)*X 2 0+(3426837307/5000000000 : ℝ)*X 2 1+(-3408455821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((5243881733/10000000000 : ℝ)*X 0 0+(2165799519/5000000000 : ℝ)*X 0 1+(1735306143/5000000000 : ℝ)*X 0 2+(5243881733/10000000000 : ℝ)*X 1 0+(2165799519/5000000000 : ℝ)*X 1 1+(1735306143/5000000000 : ℝ)*X 1 2+(5243881733/10000000000 : ℝ)*X 2 0+(2165799519/5000000000 : ℝ)*X 2 1+(1735306143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301031_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((1389/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1389/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (746951651618156711612261016701/194347103669950000000000000000000000 : ℝ) := by norm_num
    linear_combination (166925296047/500000000000 : ℝ)*(base49) + (73812462243/50000000000 : ℝ)*(base50) + (16127/100000000000 : ℝ)*(base60) + (1020096696733/200000000000 : ℝ)*(major_s2_0) + (1020096696733/200000000000 : ℝ)*(major_s2_1) + (1020096696733/200000000000 : ℝ)*(major_s2_2) + (3203377/200000000000 : ℝ)*(sp_s2_1) + (1688226062097/250000000000 : ℝ)*(sp_s2_7) + (6752906428411/1000000000000 : ℝ)*(sp_s2_8) + (6752897919989/1000000000000 : ℝ)*(sp_s2_9) + (3448026696901/1000000000000 : ℝ)*(sp_s2_12) + (16543997/1000000000000 : ℝ)*(sp_s2_19) + (4549227/250000000000 : ℝ)*(sp_s2_20) + (24525307/1000000000000 : ℝ)*(sp_s2_22) + (3448043240897/1000000000000 : ℝ)*(f.failure) + (422057652831/62500000000 : ℝ)*(f.sum) + (10336330711167313711/17144491980000000000000000000000 : ℝ)*base62 + (15966919523501/38994000000000000000000000 : ℝ)*base64 + (8846308564017/21983500000000000000000000 : ℝ)*base66 + (17156380187743/194970000000000000000000000 : ℝ)*base68 + (11087506823318678419/26521769100000000000000000000000 : ℝ)*base70 + (144645955434517/680150000000000000000000000 : ℝ)*base72 + (110904805290283/175868000000000000000000000 : ℝ)*base74 + (394092100670617/1360300000000000000000000000 : ℝ)*base76 + (13334533379232504149/29904155050000000000000000000000 : ℝ)*base78 + (13043/25000000000000000 : ℝ)*base86 + (13043/25000000000000000 : ℝ)*base88 + (13043/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6199/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(6199/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38338665130677623915751333/3738019381250000000000000000000 : ℝ) := by norm_num
    linear_combination (1109303/500000000000 : ℝ)*(base24) + (454465841381/1000000000000 : ℝ)*(base40) + (62478590309/500000000000 : ℝ)*(base50) + (87167416587/500000000000 : ℝ)*(base60) + (506415095393/200000000000 : ℝ)*(major_s2_0) + (506415095393/200000000000 : ℝ)*(major_s2_1) + (506415095393/200000000000 : ℝ)*(major_s2_2) + (2704079/500000000000 : ℝ)*(sp_s2_1) + (123446533/1000000000000 : ℝ)*(sp_s2_2) + (3352406724323/1000000000000 : ℝ)*(sp_s2_13) + (670470638393/200000000000 : ℝ)*(sp_s2_14) + (209517566199/62500000000 : ℝ)*(sp_s2_15) + (855870405399/500000000000 : ℝ)*(sp_s2_19) + (48124201/1000000000000 : ℝ)*(sp_s2_21) + (855870405399/500000000000 : ℝ)*(f.failure) + (3352406724323/1000000000000 : ℝ)*(f.sum) + (7532910931057994983/17144491980000000000000000000000 : ℝ)*base63 + (4490987526341/38994000000000000000000000 : ℝ)*base65 + (263077509319921/439670000000000000000000000 : ℝ)*base67 + (43283268134597/194970000000000000000000000 : ℝ)*base68 + (12116924460775674569/26521769100000000000000000000000 : ℝ)*base70 + (56306839044229/340075000000000000000000000 : ℝ)*base73 + (516784378273459/879340000000000000000000000 : ℝ)*base75 + (55053140795693/1360300000000000000000000000 : ℝ)*base77 + (20763919716756327901/29904155050000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (2081/12500000000000000 : ℝ)*base86 + (2081/12500000000000000 : ℝ)*base88 + (2081/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41829/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41829/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (251865156707921002049715161689/34704839941062500000000000000000000 : ℝ) := by norm_num
    linear_combination (681160795393/1000000000000 : ℝ)*(base40) + (677537241/976562500 : ℝ)*(base49) + (798698862591/500000000000 : ℝ)*(base50) + (1324294010669/250000000000 : ℝ)*(major_s2_0) + (1324294010669/250000000000 : ℝ)*(major_s2_1) + (1324294010669/250000000000 : ℝ)*(major_s2_2) + (9665633/500000000000 : ℝ)*(sp_s2_6) + (115135111/1000000000000 : ℝ)*(sp_s2_9) + (4414701/125000000000 : ℝ)*(sp_s2_14) + (23525453/1000000000000 : ℝ)*(sp_s2_15) + (7013337766417/1000000000000 : ℝ)*(sp_s2_20) + (701330244881/100000000000 : ℝ)*(sp_s2_21) + (7013199105853/1000000000000 : ℝ)*(sp_s2_22) + (1790496284273/500000000000 : ℝ)*(sp_s2_25) + (3581011899811/1000000000000 : ℝ)*(f.failure) + (7013337766417/1000000000000 : ℝ)*(f.sum) + (157578639646346779/1530758212500000000000000000000 : ℝ)*base62 + (197703148868243/243712500000000000000000000 : ℝ)*base64 + (32320393373127/157025000000000000000000000 : ℝ)*base67 + (186926549523019/121856250000000000000000000 : ℝ)*base68 + (609462038241467731/16576105687500000000000000000000 : ℝ)*base70 + (2772790369407917/1700375000000000000000000000 : ℝ)*base72 + (7587032987527/19628125000000000000000000 : ℝ)*base74 + (561280422557051/1700375000000000000000000000 : ℝ)*base76 + (7433755645802647/10680055375000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (10591/25000000000000000 : ℝ)*base87 + (10591/25000000000000000 : ℝ)*base89 + (10591/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((13603/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13603/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(43967/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(43967/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19497/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19497/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1389/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1389/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6199/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(6199/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41829/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41829/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301031_s2 p hpa hpb X hX hprev1

#print axioms solution
