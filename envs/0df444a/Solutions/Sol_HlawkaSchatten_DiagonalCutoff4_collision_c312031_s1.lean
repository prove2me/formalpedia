-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312031_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:17:17.165989+00:00
-- url     : https://prove2.me/submissions/801c7241-8656-4fde-8344-187c7ef0fdc8

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
theorem collision_support_c312031_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3037259789/10000000000 : ℝ)*x 0 + (6049559527/10000000000 : ℝ)*x 1 + (-1711852279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3037259789/10000000000 : ℝ)^37 ≤ (2186343208673/10000000000000 : ℝ)^29 := by
    have hnat : (3037259789 : ℕ)^37*10000000000000^29 ≤ 2186343208673^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037259789 10000000000 2186343208673 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6049559527/10000000000 : ℝ)^37 ≤ (52663487752059/100000000000000 : ℝ)^29 := by
    have hnat : (6049559527 : ℕ)^37*100000000000000^29 ≤ 52663487752059^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6049559527 10000000000 52663487752059 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1711852279/5000000000 : ℝ)^37 ≤ (79603375449/312500000000 : ℝ)^29 := by
    have hnat : (1711852279 : ℕ)^37*312500000000^29 ≤ 79603375449^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711852279 5000000000 79603375449 312500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3037259789/10000000000 : ℝ), (6049559527/10000000000 : ℝ), (-1711852279/5000000000 : ℝ)] ![(2186343208673/10000000000000 : ℝ), (52663487752059/100000000000000 : ℝ), (79603375449/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3037259789/10000000000 : ℝ)|^37 ≤ (2186343208673/10000000000000 : ℝ)^29
        have hw : |(3037259789/10000000000 : ℝ)|=(3037259789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6049559527/10000000000 : ℝ)|^37 ≤ (52663487752059/100000000000000 : ℝ)^29
        have hw : |(6049559527/10000000000 : ℝ)|=(6049559527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1711852279/5000000000 : ℝ)|^37 ≤ (79603375449/312500000000 : ℝ)^29
        have hw : |(-1711852279/5000000000 : ℝ)|=(1711852279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4043772609/10000000000 : ℝ)*x 0 + (2450695851/5000000000 : ℝ)*x 1 + (3711719077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4043772609/10000000000 : ℝ)^37 ≤ (15750128567593/50000000000000 : ℝ)^29 := by
    have hnat : (4043772609 : ℕ)^37*50000000000000^29 ≤ 15750128567593^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043772609 10000000000 15750128567593 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2450695851/5000000000 : ℝ)^37 ≤ (20130765394761/50000000000000 : ℝ)^29 := by
    have hnat : (2450695851 : ℕ)^37*50000000000000^29 ≤ 20130765394761^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2450695851 5000000000 20130765394761 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3711719077/10000000000 : ℝ)^37 ≤ (1129528482401/4000000000000 : ℝ)^29 := by
    have hnat : (3711719077 : ℕ)^37*4000000000000^29 ≤ 1129528482401^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711719077 10000000000 1129528482401 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4043772609/10000000000 : ℝ), (2450695851/5000000000 : ℝ), (3711719077/10000000000 : ℝ)] ![(15750128567593/50000000000000 : ℝ), (20130765394761/50000000000000 : ℝ), (1129528482401/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4043772609/10000000000 : ℝ)|^37 ≤ (15750128567593/50000000000000 : ℝ)^29
        have hw : |(4043772609/10000000000 : ℝ)|=(4043772609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2450695851/5000000000 : ℝ)|^37 ≤ (20130765394761/50000000000000 : ℝ)^29
        have hw : |(2450695851/5000000000 : ℝ)|=(2450695851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3711719077/10000000000 : ℝ)|^37 ≤ (1129528482401/4000000000000 : ℝ)^29
        have hw : |(3711719077/10000000000 : ℝ)|=(3711719077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3270472341/10000000000 : ℝ)*x 0 + (5650231613/10000000000 : ℝ)*x 1 + (914120543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3270472341/10000000000 : ℝ)^37 ≤ (48055148003/200000000000 : ℝ)^29 := by
    have hnat : (3270472341 : ℕ)^37*200000000000^29 ≤ 48055148003^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3270472341 10000000000 48055148003 200000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5650231613/10000000000 : ℝ)^37 ≤ (24134635156331/50000000000000 : ℝ)^29 := by
    have hnat : (5650231613 : ℕ)^37*50000000000000^29 ≤ 24134635156331^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5650231613 10000000000 24134635156331 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914120543/2500000000 : ℝ)^37 ≤ (554063113381/2000000000000 : ℝ)^29 := by
    have hnat : (914120543 : ℕ)^37*2000000000000^29 ≤ 554063113381^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914120543 2500000000 554063113381 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3270472341/10000000000 : ℝ), (5650231613/10000000000 : ℝ), (914120543/2500000000 : ℝ)] ![(48055148003/200000000000 : ℝ), (24134635156331/50000000000000 : ℝ), (554063113381/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3270472341/10000000000 : ℝ)|^37 ≤ (48055148003/200000000000 : ℝ)^29
        have hw : |(-3270472341/10000000000 : ℝ)|=(3270472341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5650231613/10000000000 : ℝ)|^37 ≤ (24134635156331/50000000000000 : ℝ)^29
        have hw : |(5650231613/10000000000 : ℝ)|=(5650231613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914120543/2500000000 : ℝ)|^37 ≤ (554063113381/2000000000000 : ℝ)^29
        have hw : |(914120543/2500000000 : ℝ)|=(914120543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (722854601/1250000000 : ℝ)*x 0 + (3892893/10000000000 : ℝ)*x 1 + (729194307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (722854601/1250000000 : ℝ)^37 ≤ (3107453658121/6250000000000 : ℝ)^29 := by
    have hnat : (722854601 : ℕ)^37*6250000000000^29 ≤ 3107453658121^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722854601 1250000000 3107453658121 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3892893/10000000000 : ℝ)^37 ≤ (4463319487/100000000000000 : ℝ)^29 := by
    have hnat : (3892893 : ℕ)^37*100000000000000^29 ≤ 4463319487^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3892893 10000000000 4463319487 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729194307/1250000000 : ℝ)^37 ≤ (6284534767171/12500000000000 : ℝ)^29 := by
    have hnat : (729194307 : ℕ)^37*12500000000000^29 ≤ 6284534767171^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729194307 1250000000 6284534767171 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(722854601/1250000000 : ℝ), (3892893/10000000000 : ℝ), (729194307/1250000000 : ℝ)] ![(3107453658121/6250000000000 : ℝ), (4463319487/100000000000000 : ℝ), (6284534767171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(722854601/1250000000 : ℝ)|^37 ≤ (3107453658121/6250000000000 : ℝ)^29
        have hw : |(722854601/1250000000 : ℝ)|=(722854601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3892893/10000000000 : ℝ)|^37 ≤ (4463319487/100000000000000 : ℝ)^29
        have hw : |(3892893/10000000000 : ℝ)|=(3892893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(729194307/1250000000 : ℝ)|^37 ≤ (6284534767171/12500000000000 : ℝ)^29
        have hw : |(729194307/1250000000 : ℝ)|=(729194307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2742101167/10000000000 : ℝ)*x 0 + (3291117069/5000000000 : ℝ)*x 1 + (-47960899/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2742101167/10000000000 : ℝ)^37 ≤ (1918986935399/10000000000000 : ℝ)^29 := by
    have hnat : (2742101167 : ℕ)^37*10000000000000^29 ≤ 1918986935399^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742101167 10000000000 1918986935399 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3291117069/5000000000 : ℝ)^37 ≤ (2932509455029/5000000000000 : ℝ)^29 := by
    have hnat : (3291117069 : ℕ)^37*5000000000000^29 ≤ 2932509455029^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3291117069 5000000000 2932509455029 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47960899/156250000 : ℝ)^37 ≤ (22159941533497/100000000000000 : ℝ)^29 := by
    have hnat : (47960899 : ℕ)^37*100000000000000^29 ≤ 22159941533497^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47960899 156250000 22159941533497 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2742101167/10000000000 : ℝ), (3291117069/5000000000 : ℝ), (-47960899/156250000 : ℝ)] ![(1918986935399/10000000000000 : ℝ), (2932509455029/5000000000000 : ℝ), (22159941533497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2742101167/10000000000 : ℝ)|^37 ≤ (1918986935399/10000000000000 : ℝ)^29
        have hw : |(2742101167/10000000000 : ℝ)|=(2742101167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3291117069/5000000000 : ℝ)|^37 ≤ (2932509455029/5000000000000 : ℝ)^29
        have hw : |(3291117069/5000000000 : ℝ)|=(3291117069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47960899/156250000 : ℝ)|^37 ≤ (22159941533497/100000000000000 : ℝ)^29
        have hw : |(-47960899/156250000 : ℝ)|=(47960899/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_11 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1/312500000 : ℝ)*x 0 + (9999999999/10000000000 : ℝ)*x 1 + (1/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1/312500000 : ℝ)^37 ≤ (363/25000000000000 : ℝ)^29 := by
    have hnat : (1 : ℕ)^37*25000000000000^29 ≤ 363^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 312500000 363 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999999999/10000000000 : ℝ)^37 ≤ (49999999993621/50000000000000 : ℝ)^29 := by
    have hnat : (9999999999 : ℕ)^37*50000000000000^29 ≤ 49999999993621^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 49999999993621 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1/312500000 : ℝ)^37 ≤ (363/25000000000000 : ℝ)^29 := by
    have hnat : (1 : ℕ)^37*25000000000000^29 ≤ 363^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 312500000 363 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1/312500000 : ℝ), (9999999999/10000000000 : ℝ), (1/312500000 : ℝ)] ![(363/25000000000000 : ℝ), (49999999993621/50000000000000 : ℝ), (363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1/312500000 : ℝ)|^37 ≤ (363/25000000000000 : ℝ)^29
        have hw : |(-1/312500000 : ℝ)|=(1/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9999999999/10000000000 : ℝ)|^37 ≤ (49999999993621/50000000000000 : ℝ)^29
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1/312500000 : ℝ)|^37 ≤ (363/25000000000000 : ℝ)^29
        have hw : |(1/312500000 : ℝ)|=(1/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (772225713/2000000000 : ℝ)*x 0 + (119725443/250000000 : ℝ)*x 1 + (4015143513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (772225713/2000000000 : ℝ)^37 ≤ (29696441009271/100000000000000 : ℝ)^29 := by
    have hnat : (772225713 : ℕ)^37*100000000000000^29 ≤ 29696441009271^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772225713 2000000000 29696441009271 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119725443/250000000 : ℝ)^37 ≤ (39087560501611/100000000000000 : ℝ)^29 := by
    have hnat : (119725443 : ℕ)^37*100000000000000^29 ≤ 39087560501611^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119725443 250000000 39087560501611 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4015143513/10000000000 : ℝ)^37 ≤ (31215998478157/100000000000000 : ℝ)^29 := by
    have hnat : (4015143513 : ℕ)^37*100000000000000^29 ≤ 31215998478157^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015143513 10000000000 31215998478157 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(772225713/2000000000 : ℝ), (119725443/250000000 : ℝ), (4015143513/10000000000 : ℝ)] ![(29696441009271/100000000000000 : ℝ), (39087560501611/100000000000000 : ℝ), (31215998478157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(772225713/2000000000 : ℝ)|^37 ≤ (29696441009271/100000000000000 : ℝ)^29
        have hw : |(772225713/2000000000 : ℝ)|=(772225713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119725443/250000000 : ℝ)|^37 ≤ (39087560501611/100000000000000 : ℝ)^29
        have hw : |(119725443/250000000 : ℝ)|=(119725443/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4015143513/10000000000 : ℝ)|^37 ≤ (31215998478157/100000000000000 : ℝ)^29
        have hw : |(4015143513/10000000000 : ℝ)|=(4015143513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1728088453/5000000000 : ℝ)*x 0 + (2160918761/5000000000 : ℝ)*x 1 + (608699593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1728088453/5000000000 : ℝ)^37 ≤ (5156346427337/20000000000000 : ℝ)^29 := by
    have hnat : (1728088453 : ℕ)^37*20000000000000^29 ≤ 5156346427337^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728088453 5000000000 5156346427337 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160918761/5000000000 : ℝ)^37 ≤ (34289659818957/100000000000000 : ℝ)^29 := by
    have hnat : (2160918761 : ℕ)^37*100000000000000^29 ≤ 34289659818957^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160918761 5000000000 34289659818957 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608699593/1250000000 : ℝ)^37 ≤ (39928608030577/100000000000000 : ℝ)^29 := by
    have hnat : (608699593 : ℕ)^37*100000000000000^29 ≤ 39928608030577^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608699593 1250000000 39928608030577 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1728088453/5000000000 : ℝ), (2160918761/5000000000 : ℝ), (608699593/1250000000 : ℝ)] ![(5156346427337/20000000000000 : ℝ), (34289659818957/100000000000000 : ℝ), (39928608030577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1728088453/5000000000 : ℝ)|^37 ≤ (5156346427337/20000000000000 : ℝ)^29
        have hw : |(-1728088453/5000000000 : ℝ)|=(1728088453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2160918761/5000000000 : ℝ)|^37 ≤ (34289659818957/100000000000000 : ℝ)^29
        have hw : |(2160918761/5000000000 : ℝ)|=(2160918761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(608699593/1250000000 : ℝ)|^37 ≤ (39928608030577/100000000000000 : ℝ)^29
        have hw : |(608699593/1250000000 : ℝ)|=(608699593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (765505543/1000000000 : ℝ)*x 0 + (-48922451/2500000000 : ℝ)*x 1 + (1855350333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (765505543/1000000000 : ℝ)^37 ≤ (71110558347357/100000000000000 : ℝ)^29 := by
    have hnat : (765505543 : ℕ)^37*100000000000000^29 ≤ 71110558347357^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765505543 1000000000 71110558347357 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48922451/2500000000 : ℝ)^37 ≤ (330557238009/50000000000000 : ℝ)^29 := by
    have hnat : (48922451 : ℕ)^37*50000000000000^29 ≤ 330557238009^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48922451 2500000000 330557238009 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855350333/5000000000 : ℝ)^37 ≤ (1411416357789/5000000000000 : ℝ)^29 := by
    have hnat : (1855350333 : ℕ)^37*5000000000000^29 ≤ 1411416357789^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855350333 5000000000 1411416357789 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(765505543/1000000000 : ℝ), (-48922451/2500000000 : ℝ), (1855350333/5000000000 : ℝ)] ![(71110558347357/100000000000000 : ℝ), (330557238009/50000000000000 : ℝ), (1411416357789/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(765505543/1000000000 : ℝ)|^37 ≤ (71110558347357/100000000000000 : ℝ)^29
        have hw : |(765505543/1000000000 : ℝ)|=(765505543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48922451/2500000000 : ℝ)|^37 ≤ (330557238009/50000000000000 : ℝ)^29
        have hw : |(-48922451/2500000000 : ℝ)|=(48922451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1855350333/5000000000 : ℝ)|^37 ≤ (1411416357789/5000000000000 : ℝ)^29
        have hw : |(1855350333/5000000000 : ℝ)|=(1855350333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1072349839/5000000000 : ℝ)*x 0 + (3365852351/5000000000 : ℝ)*x 1 + (-1719578417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072349839/5000000000 : ℝ)^37 ≤ (14025419575229/100000000000000 : ℝ)^29 := by
    have hnat : (1072349839 : ℕ)^37*100000000000000^29 ≤ 14025419575229^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072349839 5000000000 14025419575229 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3365852351/5000000000 : ℝ)^37 ≤ (60354725515409/100000000000000 : ℝ)^29 := by
    have hnat : (3365852351 : ℕ)^37*100000000000000^29 ≤ 60354725515409^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3365852351 5000000000 60354725515409 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1719578417/5000000000 : ℝ)^37 ≤ (5123970978507/20000000000000 : ℝ)^29 := by
    have hnat : (1719578417 : ℕ)^37*20000000000000^29 ≤ 5123970978507^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719578417 5000000000 5123970978507 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072349839/5000000000 : ℝ), (3365852351/5000000000 : ℝ), (-1719578417/5000000000 : ℝ)] ![(14025419575229/100000000000000 : ℝ), (60354725515409/100000000000000 : ℝ), (5123970978507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072349839/5000000000 : ℝ)|^37 ≤ (14025419575229/100000000000000 : ℝ)^29
        have hw : |(1072349839/5000000000 : ℝ)|=(1072349839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3365852351/5000000000 : ℝ)|^37 ≤ (60354725515409/100000000000000 : ℝ)^29
        have hw : |(3365852351/5000000000 : ℝ)|=(3365852351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1719578417/5000000000 : ℝ)|^37 ≤ (5123970978507/20000000000000 : ℝ)^29
        have hw : |(-1719578417/5000000000 : ℝ)|=(1719578417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (477357351/2000000000 : ℝ)*x 0 + (2422644021/5000000000 : ℝ)*x 1 + (16493753/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477357351/2000000000 : ℝ)^37 ≤ (16075925942413/100000000000000 : ℝ)^29 := by
    have hnat : (477357351 : ℕ)^37*100000000000000^29 ≤ 16075925942413^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477357351 2000000000 16075925942413 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422644021/5000000000 : ℝ)^37 ≤ (9918619326719/25000000000000 : ℝ)^29 := by
    have hnat : (2422644021 : ℕ)^37*25000000000000^29 ≤ 9918619326719^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422644021 5000000000 9918619326719 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16493753/31250000 : ℝ)^37 ≤ (44249596746299/100000000000000 : ℝ)^29 := by
    have hnat : (16493753 : ℕ)^37*100000000000000^29 ≤ 44249596746299^29*31250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16493753 31250000 44249596746299 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(477357351/2000000000 : ℝ), (2422644021/5000000000 : ℝ), (16493753/31250000 : ℝ)] ![(16075925942413/100000000000000 : ℝ), (9918619326719/25000000000000 : ℝ), (44249596746299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(477357351/2000000000 : ℝ)|^37 ≤ (16075925942413/100000000000000 : ℝ)^29
        have hw : |(477357351/2000000000 : ℝ)|=(477357351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2422644021/5000000000 : ℝ)|^37 ≤ (9918619326719/25000000000000 : ℝ)^29
        have hw : |(2422644021/5000000000 : ℝ)|=(2422644021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16493753/31250000 : ℝ)|^37 ≤ (44249596746299/100000000000000 : ℝ)^29
        have hw : |(16493753/31250000 : ℝ)|=(16493753/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2938280023/10000000000 : ℝ)*x 0 + (2933580469/5000000000 : ℝ)*x 1 + (931975557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2938280023/10000000000 : ℝ)^37 ≤ (20958503390517/100000000000000 : ℝ)^29 := by
    have hnat : (2938280023 : ℕ)^37*100000000000000^29 ≤ 20958503390517^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938280023 10000000000 20958503390517 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2933580469/5000000000 : ℝ)^37 ≤ (2025844290821/4000000000000 : ℝ)^29 := by
    have hnat : (2933580469 : ℕ)^37*4000000000000^29 ≤ 2025844290821^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933580469 5000000000 2025844290821 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931975557/2500000000 : ℝ)^37 ≤ (28395389326957/100000000000000 : ℝ)^29 := by
    have hnat : (931975557 : ℕ)^37*100000000000000^29 ≤ 28395389326957^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931975557 2500000000 28395389326957 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2938280023/10000000000 : ℝ), (2933580469/5000000000 : ℝ), (931975557/2500000000 : ℝ)] ![(20958503390517/100000000000000 : ℝ), (2025844290821/4000000000000 : ℝ), (28395389326957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2938280023/10000000000 : ℝ)|^37 ≤ (20958503390517/100000000000000 : ℝ)^29
        have hw : |(-2938280023/10000000000 : ℝ)|=(2938280023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2933580469/5000000000 : ℝ)|^37 ≤ (2025844290821/4000000000000 : ℝ)^29
        have hw : |(2933580469/5000000000 : ℝ)|=(2933580469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931975557/2500000000 : ℝ)|^37 ≤ (28395389326957/100000000000000 : ℝ)^29
        have hw : |(931975557/2500000000 : ℝ)|=(931975557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6705359979/10000000000 : ℝ)*x 0 + (513011/10000000000 : ℝ)*x 1 + (4871271939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6705359979/10000000000 : ℝ)^37 ≤ (15013382436219/25000000000000 : ℝ)^29 := by
    have hnat : (6705359979 : ℕ)^37*25000000000000^29 ≤ 15013382436219^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6705359979 10000000000 15013382436219 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513011/10000000000 : ℝ)^37 ≤ (336289531/100000000000000 : ℝ)^29 := by
    have hnat : (513011 : ℕ)^37*100000000000000^29 ≤ 336289531^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513011 10000000000 336289531 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4871271939/10000000000 : ℝ)^37 ≤ (39946133952443/100000000000000 : ℝ)^29 := by
    have hnat : (4871271939 : ℕ)^37*100000000000000^29 ≤ 39946133952443^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871271939 10000000000 39946133952443 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6705359979/10000000000 : ℝ), (513011/10000000000 : ℝ), (4871271939/10000000000 : ℝ)] ![(15013382436219/25000000000000 : ℝ), (336289531/100000000000000 : ℝ), (39946133952443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6705359979/10000000000 : ℝ)|^37 ≤ (15013382436219/25000000000000 : ℝ)^29
        have hw : |(6705359979/10000000000 : ℝ)|=(6705359979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513011/10000000000 : ℝ)|^37 ≤ (336289531/100000000000000 : ℝ)^29
        have hw : |(513011/10000000000 : ℝ)|=(513011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4871271939/10000000000 : ℝ)|^37 ≤ (39946133952443/100000000000000 : ℝ)^29
        have hw : |(4871271939/10000000000 : ℝ)|=(4871271939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (20477041/80000000 : ℝ)*x 0 + (6578854051/10000000000 : ℝ)*x 1 + (-649499079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20477041/80000000 : ℝ)^37 ≤ (4393956600197/25000000000000 : ℝ)^29 := by
    have hnat : (20477041 : ℕ)^37*25000000000000^29 ≤ 4393956600197^29*80000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20477041 80000000 4393956600197 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6578854051/10000000000 : ℝ)^37 ≤ (29305882799989/50000000000000 : ℝ)^29 := by
    have hnat : (6578854051 : ℕ)^37*50000000000000^29 ≤ 29305882799989^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6578854051 10000000000 29305882799989 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649499079/2000000000 : ℝ)^37 ≤ (5953101993561/25000000000000 : ℝ)^29 := by
    have hnat : (649499079 : ℕ)^37*25000000000000^29 ≤ 5953101993561^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649499079 2000000000 5953101993561 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20477041/80000000 : ℝ), (6578854051/10000000000 : ℝ), (-649499079/2000000000 : ℝ)] ![(4393956600197/25000000000000 : ℝ), (29305882799989/50000000000000 : ℝ), (5953101993561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20477041/80000000 : ℝ)|^37 ≤ (4393956600197/25000000000000 : ℝ)^29
        have hw : |(20477041/80000000 : ℝ)|=(20477041/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6578854051/10000000000 : ℝ)|^37 ≤ (29305882799989/50000000000000 : ℝ)^29
        have hw : |(6578854051/10000000000 : ℝ)|=(6578854051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-649499079/2000000000 : ℝ)|^37 ≤ (5953101993561/25000000000000 : ℝ)^29
        have hw : |(-649499079/2000000000 : ℝ)|=(649499079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312031_s1_s1_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (303011353/625000000 : ℝ)*x 0 + (4281780501/10000000000 : ℝ)*x 1 + (440259943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303011353/625000000 : ℝ)^37 ≤ (4963088694899/12500000000000 : ℝ)^29 := by
    have hnat : (303011353 : ℕ)^37*12500000000000^29 ≤ 4963088694899^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303011353 625000000 4963088694899 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4281780501/10000000000 : ℝ)^37 ≤ (33884692196609/100000000000000 : ℝ)^29 := by
    have hnat : (4281780501 : ℕ)^37*100000000000000^29 ≤ 33884692196609^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281780501 10000000000 33884692196609 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440259943/1250000000 : ℝ)^37 ≤ (5282119646729/20000000000000 : ℝ)^29 := by
    have hnat : (440259943 : ℕ)^37*20000000000000^29 ≤ 5282119646729^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440259943 1250000000 5282119646729 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(303011353/625000000 : ℝ), (4281780501/10000000000 : ℝ), (440259943/1250000000 : ℝ)] ![(4963088694899/12500000000000 : ℝ), (33884692196609/100000000000000 : ℝ), (5282119646729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(303011353/625000000 : ℝ)|^37 ≤ (4963088694899/12500000000000 : ℝ)^29
        have hw : |(303011353/625000000 : ℝ)|=(303011353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4281780501/10000000000 : ℝ)|^37 ≤ (33884692196609/100000000000000 : ℝ)^29
        have hw : |(4281780501/10000000000 : ℝ)|=(4281780501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440259943/1250000000 : ℝ)|^37 ≤ (5282119646729/20000000000000 : ℝ)^29
        have hw : |(440259943/1250000000 : ℝ)|=(440259943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312031_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((75059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(62617/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(62617/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20709/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20709/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11137/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11137/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2813/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2813/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24841/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24841/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (75059/100000 : ℝ) ^ (9/2 : ℝ) ≤ (27498720279116854681/100000000000000000000 : ℝ) := by
    have hpowers : (75059/100000 : ℝ)^9 ≤ (27498720279116854681/100000000000000000000 : ℝ)^2 := by
      have hnat : (75059 : ℕ)^9*100000000000000000000^2 ≤ 27498720279116854681^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75059 100000 27498720279116854681 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75059/100000 : ℝ)) (X := (27498720279116854681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (127498720279116854681/100000000000000000000 : ℝ) ≤ (10554696241217719/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (127498720279116854681/100000000000000000000 : ℝ)^2 ≤ (10554696241217719/10000000000000000 : ℝ)^9 := by
      have hnat : (127498720279116854681 : ℕ)^2*10000000000000000^9 ≤ 10554696241217719^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127498720279116854681 100000000000000000000 10554696241217719 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10554696241217719/10000000000000000 : ℝ)) (X := (127498720279116854681/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (77498720279116854681/50000000000000000000 : ℝ) ≤ (11022861212302101/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (77498720279116854681/50000000000000000000 : ℝ)^2 ≤ (11022861212302101/10000000000000000 : ℝ)^9 := by
      have hnat : (77498720279116854681 : ℕ)^2*10000000000000000^9 ≤ 11022861212302101^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77498720279116854681 50000000000000000000 11022861212302101 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11022861212302101/10000000000000000 : ℝ)) (X := (77498720279116854681/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(554696241217719/7505900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(234082485542191/3752950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (75059/100000 : ℝ)) (alpha := (554696241217719/7505900000000000 : ℝ)) (beta := (234082485542191/3752950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (75059/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(554696241217719/7505900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(234082485542191/3752950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (62617/100000 : ℝ) ^ (9/2 : ℝ) ≤ (3041271298280767797/25000000000000000000 : ℝ) := by
    have hpowers : (62617/100000 : ℝ)^9 ≤ (3041271298280767797/25000000000000000000 : ℝ)^2 := by
      have hnat : (62617 : ℕ)^9*25000000000000000000^2 ≤ 3041271298280767797^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62617 100000 3041271298280767797 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62617/100000 : ℝ)) (X := (3041271298280767797/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (28041271298280767797/25000000000000000000 : ℝ) ≤ (10258396634679003/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (28041271298280767797/25000000000000000000 : ℝ)^2 ≤ (10258396634679003/10000000000000000 : ℝ)^9 := by
      have hnat : (28041271298280767797 : ℕ)^2*10000000000000000^9 ≤ 10258396634679003^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28041271298280767797 25000000000000000000 10258396634679003 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10258396634679003/10000000000000000 : ℝ)) (X := (28041271298280767797/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (15541271298280767797/12500000000000000000 : ℝ) ≤ (5247917640839557/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (15541271298280767797/12500000000000000000 : ℝ)^2 ≤ (5247917640839557/5000000000000000 : ℝ)^9 := by
      have hnat : (15541271298280767797 : ℕ)^2*5000000000000000^9 ≤ 5247917640839557^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15541271298280767797 12500000000000000000 5247917640839557 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5247917640839557/5000000000000000 : ℝ)) (X := (15541271298280767797/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(258396634679003/6261700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(237438647000111/6261700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (62617/100000 : ℝ)) (alpha := (258396634679003/6261700000000000 : ℝ)) (beta := (237438647000111/6261700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (62617/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(258396634679003/6261700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(237438647000111/6261700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (20709/25000 : ℝ) ^ (9/2 : ℝ) ≤ (10713368570321947621/25000000000000000000 : ℝ) := by
    have hpowers : (20709/25000 : ℝ)^9 ≤ (10713368570321947621/25000000000000000000 : ℝ)^2 := by
      have hnat : (20709 : ℕ)^9*25000000000000000000^2 ≤ 10713368570321947621^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20709 25000 10713368570321947621 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20709/25000 : ℝ)) (X := (10713368570321947621/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (35713368570321947621/25000000000000000000 : ℝ) ≤ (2706201858978649/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (35713368570321947621/25000000000000000000 : ℝ)^2 ≤ (2706201858978649/2500000000000000 : ℝ)^9 := by
      have hnat : (35713368570321947621 : ℕ)^2*2500000000000000^9 ≤ 2706201858978649^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35713368570321947621 25000000000000000000 2706201858978649 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2706201858978649/2500000000000000 : ℝ)) (X := (35713368570321947621/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (23213368570321947621/12500000000000000000 : ℝ) ≤ (2868663439387979/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (23213368570321947621/12500000000000000000 : ℝ)^2 ≤ (2868663439387979/2500000000000000 : ℝ)^9 := by
      have hnat : (23213368570321947621 : ℕ)^2*2500000000000000^9 ≤ 2868663439387979^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23213368570321947621 12500000000000000000 2868663439387979 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2868663439387979/2500000000000000 : ℝ)) (X := (23213368570321947621/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(68733952992883/690300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16246158040933/207090000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (20709/25000 : ℝ)) (alpha := (68733952992883/690300000000000 : ℝ)) (beta := (16246158040933/207090000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (20709/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(68733952992883/690300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16246158040933/207090000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_2 : ((3037259789/10000000000 : ℝ)*X 2 0+(6049559527/10000000000 : ℝ)*X 2 1+(-1711852279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4043772609/10000000000 : ℝ)*X 0 0+(2450695851/5000000000 : ℝ)*X 0 1+(3711719077/10000000000 : ℝ)*X 0 2+(4043772609/10000000000 : ℝ)*X 1 0+(2450695851/5000000000 : ℝ)*X 1 1+(3711719077/10000000000 : ℝ)*X 1 2+(4043772609/10000000000 : ℝ)*X 2 0+(2450695851/5000000000 : ℝ)*X 2 1+(3711719077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-3270472341/10000000000 : ℝ)*X 0 0+(5650231613/10000000000 : ℝ)*X 0 1+(914120543/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((722854601/1250000000 : ℝ)*X 1 0+(3892893/10000000000 : ℝ)*X 1 1+(729194307/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2742101167/10000000000 : ℝ)*X 2 0+(3291117069/5000000000 : ℝ)*X 2 1+(-47960899/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_11 : ((-1/312500000 : ℝ)*X 0 0+(9999999999/10000000000 : ℝ)*X 0 1+(1/312500000 : ℝ)*X 0 2+(-1/312500000 : ℝ)*X 2 0+(9999999999/10000000000 : ℝ)*X 2 1+(1/312500000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_11 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((772225713/2000000000 : ℝ)*X 0 0+(119725443/250000000 : ℝ)*X 0 1+(4015143513/10000000000 : ℝ)*X 0 2+(772225713/2000000000 : ℝ)*X 1 0+(119725443/250000000 : ℝ)*X 1 1+(4015143513/10000000000 : ℝ)*X 1 2+(772225713/2000000000 : ℝ)*X 2 0+(119725443/250000000 : ℝ)*X 2 1+(4015143513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1728088453/5000000000 : ℝ)*X 0 0+(2160918761/5000000000 : ℝ)*X 0 1+(608699593/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((765505543/1000000000 : ℝ)*X 1 0+(-48922451/2500000000 : ℝ)*X 1 1+(1855350333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1072349839/5000000000 : ℝ)*X 2 0+(3365852351/5000000000 : ℝ)*X 2 1+(-1719578417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((477357351/2000000000 : ℝ)*X 0 0+(2422644021/5000000000 : ℝ)*X 0 1+(16493753/31250000 : ℝ)*X 0 2+(477357351/2000000000 : ℝ)*X 1 0+(2422644021/5000000000 : ℝ)*X 1 1+(16493753/31250000 : ℝ)*X 1 2+(477357351/2000000000 : ℝ)*X 2 0+(2422644021/5000000000 : ℝ)*X 2 1+(16493753/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2938280023/10000000000 : ℝ)*X 0 0+(2933580469/5000000000 : ℝ)*X 0 1+(931975557/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6705359979/10000000000 : ℝ)*X 1 0+(513011/10000000000 : ℝ)*X 1 1+(4871271939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((20477041/80000000 : ℝ)*X 2 0+(6578854051/10000000000 : ℝ)*X 2 1+(-649499079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((303011353/625000000 : ℝ)*X 0 0+(4281780501/10000000000 : ℝ)*X 0 1+(440259943/1250000000 : ℝ)*X 0 2+(303011353/625000000 : ℝ)*X 1 0+(4281780501/10000000000 : ℝ)*X 1 1+(440259943/1250000000 : ℝ)*X 1 2+(303011353/625000000 : ℝ)*X 2 0+(4281780501/10000000000 : ℝ)*X 2 1+(440259943/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312031_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11137/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11137/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12030266744713615357479/626170000000000000000000000 : ℝ) := by norm_num
    linear_combination (255481/25000000000 : ℝ)*(base23) + (35285648779/1000000000000 : ℝ)*(base40) + (2184833598629/1000000000000 : ℝ)*(base50) + (191561644867/25000000000 : ℝ)*(major_s1_0) + (153252086607/20000000000 : ℝ)*(major_s1_1) + (191561644867/25000000000 : ℝ)*(major_s1_2) + (10734083008973/1000000000000 : ℝ)*(sp_s1_7) + (10734230754763/1000000000000 : ℝ)*(sp_s1_8) + (10734186370299/1000000000000 : ℝ)*(sp_s1_9) + (13853567/100000000000 : ℝ)*(sp_s1_11) + (4590623774193/1000000000000 : ℝ)*(sp_s1_13) + (4270653/125000000000 : ℝ)*(sp_s1_16) + (70656247/1000000000000 : ℝ)*(sp_s1_20) + (14774579/100000000000 : ℝ)*(sp_s1_21) + (114767360761/25000000000 : ℝ)*(f.failure) + (10734230754763/1000000000000 : ℝ)*(f.sum) + (657594162401275361/1080612877500000000000000000000 : ℝ)*base62 + (48318484289143/207090000000000000000000000 : ℝ)*base65 + (1315188864793/3913562500000000000000000 : ℝ)*base66 + (10061407073771/34515000000000000000000000 : ℝ)*base69 + (514571576592787019/3108793662000000000000000000000 : ℝ)*base70 + (214378688161413/750590000000000000000000000 : ℝ)*base73 + (814888934677/3913562500000000000000000 : ℝ)*base74 + (36436734983113/375295000000000000000000000 : ℝ)*base77 + (1806633498617389603/2349984701500000000000000000000 : ℝ)*base78 + (793/2500000000000000 : ℝ)*base87 + (793/2500000000000000 : ℝ)*base89 + (793/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2813/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2813/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (311613234766492868313314070787/27036573990757500000000000000000000 : ℝ) := by norm_num
    linear_combination (237869692613/500000000000 : ℝ)*(base40) + (83101833237/1000000000000 : ℝ)*(base50) + (48684712279/200000000000 : ℝ)*(base60) + (1050975105359/500000000000 : ℝ)*(major_s1_0) + (1050975105359/500000000000 : ℝ)*(major_s1_1) + (1050975105359/500000000000 : ℝ)*(major_s1_2) + (26927771/500000000000 : ℝ)*(sp_s1_2) + (48852209/1000000000000 : ℝ)*(sp_s1_13) + (588917542327/200000000000 : ℝ)*(sp_s1_14) + (58890015889/20000000000 : ℝ)*(sp_s1_15) + (5750993621/1953125000 : ℝ)*(sp_s1_16) + (251852003143/200000000000 : ℝ)*(sp_s1_20) + (17383437/200000000000 : ℝ)*(sp_s1_22) + (1256107/50000000000 : ℝ)*(sp_s1_23) + (314827216981/250000000000 : ℝ)*(f.failure) + (588917542327/200000000000 : ℝ)*(f.sum) + (889447454157624191/10806128775000000000000000000000 : ℝ)*base62 + (53756355553037/103545000000000000000000000 : ℝ)*base65 + (240195511661001/782712500000000000000000000 : ℝ)*base67 + (38050977282689/172575000000000000000000000 : ℝ)*base68 + (2255379929093240489/19429960387500000000000000000000 : ℝ)*base70 + (1143129410476849/1876475000000000000000000000 : ℝ)*base73 + (2105670483728083/3130850000000000000000000000 : ℝ)*base75 + (1302298525097661/3752950000000000000000000000 : ℝ)*base77 + (30036774864136154271/117499235075000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (347/25000000000000000 : ℝ)*base86 + (347/25000000000000000 : ℝ)*base88 + (347/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24841/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24841/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4997456184412578634392786255799/405548609861362500000000000000000000 : ℝ) := by norm_num
    linear_combination (32018693031/40000000000 : ℝ)*(base40) + (209896911497/100000000000 : ℝ)*(base50) + (7678447709983/1000000000000 : ℝ)*(major_s1_0) + (14440102607393/1000000000000 : ℝ)*(major_s1_1) + (7678447709983/1000000000000 : ℝ)*(major_s1_2) + (19530741/500000000000 : ℝ)*(sp_s1_6) + (302109247/1000000000000 : ℝ)*(sp_s1_9) + (676165489741/100000000000 : ℝ)*(sp_s1_11) + (65473537/1000000000000 : ℝ)*(sp_s1_15) + (86791947/1000000000000 : ℝ)*(sp_s1_16) + (10756621884617/1000000000000 : ℝ)*(sp_s1_21) + (268913910277/25000000000 : ℝ)*(sp_s1_22) + (10756232983423/1000000000000 : ℝ)*(sp_s1_23) + (4600230366293/1000000000000 : ℝ)*(sp_s1_27) + (71879209809/15625000000 : ℝ)*(f.failure) + (10756621884617/1000000000000 : ℝ)*(f.sum) + (4238341605295104083/21612257550000000000000000000000 : ℝ)*base63 + (40368567256301/103545000000000000000000000 : ℝ)*base65 + (1743562975497283/6261700000000000000000000000 : ℝ)*base67 + (328708775624029/690300000000000000000000000 : ℝ)*base69 + (15335490569742133313/155439683100000000000000000000000 : ℝ)*base71 + (1496850337523693/3752950000000000000000000000 : ℝ)*base73 + (1953893580038581/6261700000000000000000000000 : ℝ)*base75 + (2126051329700777/7505900000000000000000000000 : ℝ)*base77 + (108203105753461436429/469996940300000000000000000000000 : ℝ)*base79 + (2359/3125000000000000 : ℝ)*base87 + (2359/3125000000000000 : ℝ)*base89 + (2359/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((75059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(62617/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(62617/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20709/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20709/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11137/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11137/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2813/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2813/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24841/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24841/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312031_s1 p hpa hpb X hX hprev0

#print axioms solution
