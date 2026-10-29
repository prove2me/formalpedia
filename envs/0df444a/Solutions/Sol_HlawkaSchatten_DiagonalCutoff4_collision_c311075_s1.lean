-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311075_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:02:33.755867+00:00
-- url     : https://prove2.me/submissions/34864dfd-0534-4e3b-9342-e99be255eae9

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
theorem collision_support_c311075_s1_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-230475543/2500000000 : ℝ)*x 0 + (-642355903/1000000000 : ℝ)*x 1 + (956357193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230475543/2500000000 : ℝ)^9 ≤ (72895468621/1562500000000 : ℝ)^7 := by
    have hnat : (230475543 : ℕ)^9*1562500000000^7 ≤ 72895468621^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230475543 2500000000 72895468621 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642355903/1000000000 : ℝ)^9 ≤ (56604961124769/100000000000000 : ℝ)^7 := by
    have hnat : (642355903 : ℕ)^9*100000000000000^7 ≤ 56604961124769^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642355903 1000000000 56604961124769 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956357193/2000000000 : ℝ)^9 ≤ (38729728870867/100000000000000 : ℝ)^7 := by
    have hnat : (956357193 : ℕ)^9*100000000000000^7 ≤ 38729728870867^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956357193 2000000000 38729728870867 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230475543/2500000000 : ℝ), (-642355903/1000000000 : ℝ), (956357193/2000000000 : ℝ)] ![(72895468621/1562500000000 : ℝ), (56604961124769/100000000000000 : ℝ), (38729728870867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230475543/2500000000 : ℝ)|^9 ≤ (72895468621/1562500000000 : ℝ)^7
        have hw : |(-230475543/2500000000 : ℝ)|=(230475543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-642355903/1000000000 : ℝ)|^9 ≤ (56604961124769/100000000000000 : ℝ)^7
        have hw : |(-642355903/1000000000 : ℝ)|=(642355903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(956357193/2000000000 : ℝ)|^9 ≤ (38729728870867/100000000000000 : ℝ)^7
        have hw : |(956357193/2000000000 : ℝ)|=(956357193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5279459539/10000000000 : ℝ)*x 0 + (-1934014881/5000000000 : ℝ)*x 1 + (-890592491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279459539/10000000000 : ℝ)^9 ≤ (43987503383309/100000000000000 : ℝ)^7 := by
    have hnat : (5279459539 : ℕ)^9*100000000000000^7 ≤ 43987503383309^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279459539 10000000000 43987503383309 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934014881/5000000000 : ℝ)^9 ≤ (29486943111193/100000000000000 : ℝ)^7 := by
    have hnat : (1934014881 : ℕ)^9*100000000000000^7 ≤ 29486943111193^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934014881 5000000000 29486943111193 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890592491/2500000000 : ℝ)^9 ≤ (26525553490927/100000000000000 : ℝ)^7 := by
    have hnat : (890592491 : ℕ)^9*100000000000000^7 ≤ 26525553490927^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890592491 2500000000 26525553490927 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279459539/10000000000 : ℝ), (-1934014881/5000000000 : ℝ), (-890592491/2500000000 : ℝ)] ![(43987503383309/100000000000000 : ℝ), (29486943111193/100000000000000 : ℝ), (26525553490927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279459539/10000000000 : ℝ)|^9 ≤ (43987503383309/100000000000000 : ℝ)^7
        have hw : |(5279459539/10000000000 : ℝ)|=(5279459539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1934014881/5000000000 : ℝ)|^9 ≤ (29486943111193/100000000000000 : ℝ)^7
        have hw : |(-1934014881/5000000000 : ℝ)|=(1934014881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890592491/2500000000 : ℝ)|^9 ≤ (26525553490927/100000000000000 : ℝ)^7
        have hw : |(-890592491/2500000000 : ℝ)|=(890592491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2794251181/10000000000 : ℝ)*x 0 + (-143653231/625000000 : ℝ)*x 1 + (7194755241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2794251181/10000000000 : ℝ)^9 ≤ (155290739029/800000000000 : ℝ)^7 := by
    have hnat : (2794251181 : ℕ)^9*800000000000^7 ≤ 155290739029^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794251181 10000000000 155290739029 800000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143653231/625000000 : ℝ)^9 ≤ (15100396366419/100000000000000 : ℝ)^7 := by
    have hnat : (143653231 : ℕ)^9*100000000000000^7 ≤ 15100396366419^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143653231 625000000 15100396366419 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7194755241/10000000000 : ℝ)^9 ≤ (4093016327129/6250000000000 : ℝ)^7 := by
    have hnat : (7194755241 : ℕ)^9*6250000000000^7 ≤ 4093016327129^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7194755241 10000000000 4093016327129 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2794251181/10000000000 : ℝ), (-143653231/625000000 : ℝ), (7194755241/10000000000 : ℝ)] ![(155290739029/800000000000 : ℝ), (15100396366419/100000000000000 : ℝ), (4093016327129/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2794251181/10000000000 : ℝ)|^9 ≤ (155290739029/800000000000 : ℝ)^7
        have hw : |(2794251181/10000000000 : ℝ)|=(2794251181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-143653231/625000000 : ℝ)|^9 ≤ (15100396366419/100000000000000 : ℝ)^7
        have hw : |(-143653231/625000000 : ℝ)|=(143653231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7194755241/10000000000 : ℝ)|^9 ≤ (4093016327129/6250000000000 : ℝ)^7
        have hw : |(7194755241/10000000000 : ℝ)|=(7194755241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-206677149/5000000000 : ℝ)*x 0 + (-3714651177/5000000000 : ℝ)*x 1 + (98237571/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206677149/5000000000 : ℝ)^9 ≤ (1663359094521/100000000000000 : ℝ)^7 := by
    have hnat : (206677149 : ℕ)^9*100000000000000^7 ≤ 1663359094521^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206677149 5000000000 1663359094521 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3714651177/5000000000 : ℝ)^9 ≤ (68245817894457/100000000000000 : ℝ)^7 := by
    have hnat : (3714651177 : ℕ)^9*100000000000000^7 ≤ 68245817894457^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714651177 5000000000 68245817894457 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98237571/250000000 : ℝ)^9 ≤ (15045411501499/50000000000000 : ℝ)^7 := by
    have hnat : (98237571 : ℕ)^9*50000000000000^7 ≤ 15045411501499^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98237571 250000000 15045411501499 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206677149/5000000000 : ℝ), (-3714651177/5000000000 : ℝ), (98237571/250000000 : ℝ)] ![(1663359094521/100000000000000 : ℝ), (68245817894457/100000000000000 : ℝ), (15045411501499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206677149/5000000000 : ℝ)|^9 ≤ (1663359094521/100000000000000 : ℝ)^7
        have hw : |(-206677149/5000000000 : ℝ)|=(206677149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3714651177/5000000000 : ℝ)|^9 ≤ (68245817894457/100000000000000 : ℝ)^7
        have hw : |(-3714651177/5000000000 : ℝ)|=(3714651177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(98237571/250000000 : ℝ)|^9 ≤ (15045411501499/50000000000000 : ℝ)^7
        have hw : |(98237571/250000000 : ℝ)|=(98237571/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (167726637/250000000 : ℝ)*x 0 + (2897031467/10000000000 : ℝ)*x 1 + (2838321179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167726637/250000000 : ℝ)^9 ≤ (29930012677543/50000000000000 : ℝ)^7 := by
    have hnat : (167726637 : ℕ)^9*50000000000000^7 ≤ 29930012677543^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167726637 250000000 29930012677543 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2897031467/10000000000 : ℝ)^9 ≤ (20334128272763/100000000000000 : ℝ)^7 := by
    have hnat : (2897031467 : ℕ)^9*100000000000000^7 ≤ 20334128272763^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897031467 10000000000 20334128272763 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2838321179/10000000000 : ℝ)^9 ≤ (19805846360763/100000000000000 : ℝ)^7 := by
    have hnat : (2838321179 : ℕ)^9*100000000000000^7 ≤ 19805846360763^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838321179 10000000000 19805846360763 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167726637/250000000 : ℝ), (2897031467/10000000000 : ℝ), (2838321179/10000000000 : ℝ)] ![(29930012677543/50000000000000 : ℝ), (20334128272763/100000000000000 : ℝ), (19805846360763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167726637/250000000 : ℝ)|^9 ≤ (29930012677543/50000000000000 : ℝ)^7
        have hw : |(167726637/250000000 : ℝ)|=(167726637/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2897031467/10000000000 : ℝ)|^9 ≤ (20334128272763/100000000000000 : ℝ)^7
        have hw : |(2897031467/10000000000 : ℝ)|=(2897031467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2838321179/10000000000 : ℝ)|^9 ≤ (19805846360763/100000000000000 : ℝ)^7
        have hw : |(2838321179/10000000000 : ℝ)|=(2838321179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1081991981/2000000000 : ℝ)*x 0 + (-3741861989/10000000000 : ℝ)*x 1 + (-3544383437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081991981/2000000000 : ℝ)^9 ≤ (5673796916993/12500000000000 : ℝ)^7 := by
    have hnat : (1081991981 : ℕ)^9*12500000000000^7 ≤ 5673796916993^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081991981 2000000000 5673796916993 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3741861989/10000000000 : ℝ)^9 ≤ (3532017561167/12500000000000 : ℝ)^7 := by
    have hnat : (3741861989 : ℕ)^9*12500000000000^7 ≤ 3532017561167^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741861989 10000000000 3532017561167 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3544383437/10000000000 : ℝ)^9 ≤ (5270696831637/20000000000000 : ℝ)^7 := by
    have hnat : (3544383437 : ℕ)^9*20000000000000^7 ≤ 5270696831637^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3544383437 10000000000 5270696831637 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081991981/2000000000 : ℝ), (-3741861989/10000000000 : ℝ), (-3544383437/10000000000 : ℝ)] ![(5673796916993/12500000000000 : ℝ), (3532017561167/12500000000000 : ℝ), (5270696831637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081991981/2000000000 : ℝ)|^9 ≤ (5673796916993/12500000000000 : ℝ)^7
        have hw : |(1081991981/2000000000 : ℝ)|=(1081991981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3741861989/10000000000 : ℝ)|^9 ≤ (3532017561167/12500000000000 : ℝ)^7
        have hw : |(-3741861989/10000000000 : ℝ)|=(3741861989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3544383437/10000000000 : ℝ)|^9 ≤ (5270696831637/20000000000000 : ℝ)^7
        have hw : |(-3544383437/10000000000 : ℝ)|=(3544383437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (10968683/100000000 : ℝ)*x 0 + (-556959/8000000 : ℝ)*x 1 + (1160749271/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10968683/100000000 : ℝ)^9 ≤ (5833281161619/100000000000000 : ℝ)^7 := by
    have hnat : (10968683 : ℕ)^9*100000000000000^7 ≤ 5833281161619^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10968683 100000000 5833281161619 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556959/8000000 : ℝ)^9 ≤ (3251513737651/100000000000000 : ℝ)^7 := by
    have hnat : (556959 : ℕ)^9*100000000000000^7 ≤ 3251513737651^7*8000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556959 8000000 3251513737651 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1160749271/1250000000 : ℝ)^9 ≤ (45457602542291/50000000000000 : ℝ)^7 := by
    have hnat : (1160749271 : ℕ)^9*50000000000000^7 ≤ 45457602542291^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160749271 1250000000 45457602542291 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10968683/100000000 : ℝ), (-556959/8000000 : ℝ), (1160749271/1250000000 : ℝ)] ![(5833281161619/100000000000000 : ℝ), (3251513737651/100000000000000 : ℝ), (45457602542291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10968683/100000000 : ℝ)|^9 ≤ (5833281161619/100000000000000 : ℝ)^7
        have hw : |(10968683/100000000 : ℝ)|=(10968683/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556959/8000000 : ℝ)|^9 ≤ (3251513737651/100000000000000 : ℝ)^7
        have hw : |(-556959/8000000 : ℝ)|=(556959/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1160749271/1250000000 : ℝ)|^9 ≤ (45457602542291/50000000000000 : ℝ)^7
        have hw : |(1160749271/1250000000 : ℝ)|=(1160749271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-42976781/2500000000 : ℝ)*x 0 + (-6112822663/10000000000 : ℝ)*x 1 + (549895367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42976781/2500000000 : ℝ)^9 ≤ (269191987449/50000000000000 : ℝ)^7 := by
    have hnat : (42976781 : ℕ)^9*50000000000000^7 ≤ 269191987449^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42976781 2500000000 269191987449 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6112822663/10000000000 : ℝ)^9 ≤ (26554493909109/50000000000000 : ℝ)^7 := by
    have hnat : (6112822663 : ℕ)^9*50000000000000^7 ≤ 26554493909109^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6112822663 10000000000 26554493909109 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549895367/1000000000 : ℝ)^9 ≤ (9270525639509/20000000000000 : ℝ)^7 := by
    have hnat : (549895367 : ℕ)^9*20000000000000^7 ≤ 9270525639509^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549895367 1000000000 9270525639509 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42976781/2500000000 : ℝ), (-6112822663/10000000000 : ℝ), (549895367/1000000000 : ℝ)] ![(269191987449/50000000000000 : ℝ), (26554493909109/50000000000000 : ℝ), (9270525639509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42976781/2500000000 : ℝ)|^9 ≤ (269191987449/50000000000000 : ℝ)^7
        have hw : |(-42976781/2500000000 : ℝ)|=(42976781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6112822663/10000000000 : ℝ)|^9 ≤ (26554493909109/50000000000000 : ℝ)^7
        have hw : |(-6112822663/10000000000 : ℝ)|=(6112822663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549895367/1000000000 : ℝ)|^9 ≤ (9270525639509/20000000000000 : ℝ)^7
        have hw : |(549895367/1000000000 : ℝ)|=(549895367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1907705543/2500000000 : ℝ)*x 0 + (238852381/1000000000 : ℝ)*x 1 + (526647941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1907705543/2500000000 : ℝ)^9 ≤ (14127010919041/20000000000000 : ℝ)^7 := by
    have hnat : (1907705543 : ℕ)^9*20000000000000^7 ≤ 14127010919041^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907705543 2500000000 14127010919041 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238852381/1000000000 : ℝ)^9 ≤ (158654469263/1000000000000 : ℝ)^7 := by
    have hnat : (238852381 : ℕ)^9*1000000000000^7 ≤ 158654469263^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238852381 1000000000 158654469263 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526647941/2500000000 : ℝ)^9 ≤ (843718654187/6250000000000 : ℝ)^7 := by
    have hnat : (526647941 : ℕ)^9*6250000000000^7 ≤ 843718654187^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526647941 2500000000 843718654187 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1907705543/2500000000 : ℝ), (238852381/1000000000 : ℝ), (526647941/2500000000 : ℝ)] ![(14127010919041/20000000000000 : ℝ), (158654469263/1000000000000 : ℝ), (843718654187/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1907705543/2500000000 : ℝ)|^9 ≤ (14127010919041/20000000000000 : ℝ)^7
        have hw : |(1907705543/2500000000 : ℝ)|=(1907705543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238852381/1000000000 : ℝ)|^9 ≤ (158654469263/1000000000000 : ℝ)^7
        have hw : |(238852381/1000000000 : ℝ)|=(238852381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526647941/2500000000 : ℝ)|^9 ≤ (843718654187/6250000000000 : ℝ)^7
        have hw : |(526647941/2500000000 : ℝ)|=(526647941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3003820377/5000000000 : ℝ)*x 0 + (-234015641/625000000 : ℝ)*x 1 + (-283585369/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3003820377/5000000000 : ℝ)^9 ≤ (10387391702363/20000000000000 : ℝ)^7 := by
    have hnat : (3003820377 : ℕ)^9*20000000000000^7 ≤ 10387391702363^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003820377 5000000000 10387391702363 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234015641/625000000 : ℝ)^9 ≤ (3534916252867/12500000000000 : ℝ)^7 := by
    have hnat : (234015641 : ℕ)^9*12500000000000^7 ≤ 3534916252867^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234015641 625000000 3534916252867 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283585369/1000000000 : ℝ)^9 ≤ (4945927864583/25000000000000 : ℝ)^7 := by
    have hnat : (283585369 : ℕ)^9*25000000000000^7 ≤ 4945927864583^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283585369 1000000000 4945927864583 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3003820377/5000000000 : ℝ), (-234015641/625000000 : ℝ), (-283585369/1000000000 : ℝ)] ![(10387391702363/20000000000000 : ℝ), (3534916252867/12500000000000 : ℝ), (4945927864583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3003820377/5000000000 : ℝ)|^9 ≤ (10387391702363/20000000000000 : ℝ)^7
        have hw : |(3003820377/5000000000 : ℝ)|=(3003820377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234015641/625000000 : ℝ)|^9 ≤ (3534916252867/12500000000000 : ℝ)^7
        have hw : |(-234015641/625000000 : ℝ)|=(234015641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283585369/1000000000 : ℝ)|^9 ≤ (4945927864583/25000000000000 : ℝ)^7
        have hw : |(-283585369/1000000000 : ℝ)|=(283585369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (128583533/1000000000 : ℝ)*x 0 + (-1067166747/10000000000 : ℝ)*x 1 + (8990537901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128583533/1000000000 : ℝ)^9 ≤ (7155943191901/100000000000000 : ℝ)^7 := by
    have hnat : (128583533 : ℕ)^9*100000000000000^7 ≤ 7155943191901^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128583533 1000000000 7155943191901 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067166747/10000000000 : ℝ)^9 ≤ (5630984933343/100000000000000 : ℝ)^7 := by
    have hnat : (1067166747 : ℕ)^9*100000000000000^7 ≤ 5630984933343^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067166747 10000000000 5630984933343 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8990537901/10000000000 : ℝ)^9 ≤ (17442614372561/20000000000000 : ℝ)^7 := by
    have hnat : (8990537901 : ℕ)^9*20000000000000^7 ≤ 17442614372561^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8990537901 10000000000 17442614372561 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128583533/1000000000 : ℝ), (-1067166747/10000000000 : ℝ), (8990537901/10000000000 : ℝ)] ![(7155943191901/100000000000000 : ℝ), (5630984933343/100000000000000 : ℝ), (17442614372561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128583533/1000000000 : ℝ)|^9 ≤ (7155943191901/100000000000000 : ℝ)^7
        have hw : |(128583533/1000000000 : ℝ)|=(128583533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067166747/10000000000 : ℝ)|^9 ≤ (5630984933343/100000000000000 : ℝ)^7
        have hw : |(-1067166747/10000000000 : ℝ)|=(1067166747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8990537901/10000000000 : ℝ)|^9 ≤ (17442614372561/20000000000000 : ℝ)^7
        have hw : |(8990537901/10000000000 : ℝ)|=(8990537901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-209207927/10000000000 : ℝ)*x 0 + (-7321757739/10000000000 : ℝ)*x 1 + (2077488447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209207927/10000000000 : ℝ)^9 ≤ (693016090029/100000000000000 : ℝ)^7 := by
    have hnat : (209207927 : ℕ)^9*100000000000000^7 ≤ 693016090029^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209207927 10000000000 693016090029 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7321757739/10000000000 : ℝ)^9 ≤ (16744571429743/25000000000000 : ℝ)^7 := by
    have hnat : (7321757739 : ℕ)^9*25000000000000^7 ≤ 16744571429743^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7321757739 10000000000 16744571429743 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077488447/5000000000 : ℝ)^9 ≤ (32328698181811/100000000000000 : ℝ)^7 := by
    have hnat : (2077488447 : ℕ)^9*100000000000000^7 ≤ 32328698181811^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077488447 5000000000 32328698181811 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209207927/10000000000 : ℝ), (-7321757739/10000000000 : ℝ), (2077488447/5000000000 : ℝ)] ![(693016090029/100000000000000 : ℝ), (16744571429743/25000000000000 : ℝ), (32328698181811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209207927/10000000000 : ℝ)|^9 ≤ (693016090029/100000000000000 : ℝ)^7
        have hw : |(-209207927/10000000000 : ℝ)|=(209207927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7321757739/10000000000 : ℝ)|^9 ≤ (16744571429743/25000000000000 : ℝ)^7
        have hw : |(-7321757739/10000000000 : ℝ)|=(7321757739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2077488447/5000000000 : ℝ)|^9 ≤ (32328698181811/100000000000000 : ℝ)^7
        have hw : |(2077488447/5000000000 : ℝ)|=(2077488447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7828333413/10000000000 : ℝ)*x 0 + (2205492969/10000000000 : ℝ)*x 1 + (2007166537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7828333413/10000000000 : ℝ)^9 ≤ (72994328598151/100000000000000 : ℝ)^7 := by
    have hnat : (7828333413 : ℕ)^9*100000000000000^7 ≤ 72994328598151^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7828333413 10000000000 72994328598151 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205492969/10000000000 : ℝ)^9 ≤ (1431976435163/10000000000000 : ℝ)^7 := by
    have hnat : (2205492969 : ℕ)^9*10000000000000^7 ≤ 1431976435163^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205492969 10000000000 1431976435163 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007166537/10000000000 : ℝ)^9 ≤ (12685907034659/100000000000000 : ℝ)^7 := by
    have hnat : (2007166537 : ℕ)^9*100000000000000^7 ≤ 12685907034659^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007166537 10000000000 12685907034659 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7828333413/10000000000 : ℝ), (2205492969/10000000000 : ℝ), (2007166537/10000000000 : ℝ)] ![(72994328598151/100000000000000 : ℝ), (1431976435163/10000000000000 : ℝ), (12685907034659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7828333413/10000000000 : ℝ)|^9 ≤ (72994328598151/100000000000000 : ℝ)^7
        have hw : |(7828333413/10000000000 : ℝ)|=(7828333413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205492969/10000000000 : ℝ)|^9 ≤ (1431976435163/10000000000000 : ℝ)^7
        have hw : |(2205492969/10000000000 : ℝ)|=(2205492969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2007166537/10000000000 : ℝ)|^9 ≤ (12685907034659/100000000000000 : ℝ)^7
        have hw : |(2007166537/10000000000 : ℝ)|=(2007166537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4630647263/10000000000 : ℝ)*x 0 + (-4433401647/10000000000 : ℝ)*x 1 + (-3684118233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4630647263/10000000000 : ℝ)^9 ≤ (9290749827373/25000000000000 : ℝ)^7 := by
    have hnat : (4630647263 : ℕ)^9*25000000000000^7 ≤ 9290749827373^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4630647263 10000000000 9290749827373 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433401647/10000000000 : ℝ)^9 ≤ (8785061853527/25000000000000 : ℝ)^7 := by
    have hnat : (4433401647 : ℕ)^9*25000000000000^7 ≤ 8785061853527^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433401647 10000000000 8785061853527 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3684118233/10000000000 : ℝ)^9 ≤ (13848376630503/50000000000000 : ℝ)^7 := by
    have hnat : (3684118233 : ℕ)^9*50000000000000^7 ≤ 13848376630503^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3684118233 10000000000 13848376630503 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4630647263/10000000000 : ℝ), (-4433401647/10000000000 : ℝ), (-3684118233/10000000000 : ℝ)] ![(9290749827373/25000000000000 : ℝ), (8785061853527/25000000000000 : ℝ), (13848376630503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4630647263/10000000000 : ℝ)|^9 ≤ (9290749827373/25000000000000 : ℝ)^7
        have hw : |(4630647263/10000000000 : ℝ)|=(4630647263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4433401647/10000000000 : ℝ)|^9 ≤ (8785061853527/25000000000000 : ℝ)^7
        have hw : |(-4433401647/10000000000 : ℝ)|=(4433401647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3684118233/10000000000 : ℝ)|^9 ≤ (13848376630503/50000000000000 : ℝ)^7
        have hw : |(-3684118233/10000000000 : ℝ)|=(3684118233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311075_s1_s1_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (77959081/200000000 : ℝ)*x 0 + (-117768827/1250000000 : ℝ)*x 1 + (7189090103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77959081/200000000 : ℝ)^9 ≤ (29780564083017/100000000000000 : ℝ)^7 := by
    have hnat : (77959081 : ℕ)^9*100000000000000^7 ≤ 29780564083017^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77959081 200000000 29780564083017 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117768827/1250000000 : ℝ)^9 ≤ (149920797159/3125000000000 : ℝ)^7 := by
    have hnat : (117768827 : ℕ)^9*3125000000000^7 ≤ 149920797159^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117768827 1250000000 149920797159 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7189090103/10000000000 : ℝ)^9 ≤ (65421970392151/100000000000000 : ℝ)^7 := by
    have hnat : (7189090103 : ℕ)^9*100000000000000^7 ≤ 65421970392151^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7189090103 10000000000 65421970392151 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(77959081/200000000 : ℝ), (-117768827/1250000000 : ℝ), (7189090103/10000000000 : ℝ)] ![(29780564083017/100000000000000 : ℝ), (149920797159/3125000000000 : ℝ), (65421970392151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(77959081/200000000 : ℝ)|^9 ≤ (29780564083017/100000000000000 : ℝ)^7
        have hw : |(77959081/200000000 : ℝ)|=(77959081/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117768827/1250000000 : ℝ)|^9 ≤ (149920797159/3125000000000 : ℝ)^7
        have hw : |(-117768827/1250000000 : ℝ)|=(117768827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7189090103/10000000000 : ℝ)|^9 ≤ (65421970392151/100000000000000 : ℝ)^7
        have hw : |(7189090103/10000000000 : ℝ)|=(7189090103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311075_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((74727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-85531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-85531/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8081/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8081/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((36661/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36661/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-57643/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-57643/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20779/50000 : ℝ)*X 1 2) := by
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
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (74727/100000 : ℝ) ^ (71/16 : ℝ) ≤ (27450901814412033149/100000000000000000000 : ℝ) := by
    have hpowers : (74727/100000 : ℝ)^71 ≤ (27450901814412033149/100000000000000000000 : ℝ)^16 := by
      have hnat : (74727 : ℕ)^71*100000000000000000000^16 ≤ 27450901814412033149^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74727 100000 27450901814412033149 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74727/100000 : ℝ)) (X := (27450901814412033149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (127450901814412033149/100000000000000000000 : ℝ) ≤ (10561831824333983/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (127450901814412033149/100000000000000000000 : ℝ)^16 ≤ (10561831824333983/10000000000000000 : ℝ)^71 := by
      have hnat : (127450901814412033149 : ℕ)^16*10000000000000000^71 ≤ 10561831824333983^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127450901814412033149 100000000000000000000 10561831824333983 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10561831824333983/10000000000000000 : ℝ)) (X := (127450901814412033149/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (77450901814412033149/50000000000000000000 : ℝ) ≤ (11036455793798837/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (77450901814412033149/50000000000000000000 : ℝ)^16 ≤ (11036455793798837/10000000000000000 : ℝ)^71 := by
      have hnat : (77450901814412033149 : ℕ)^16*10000000000000000^71 ≤ 11036455793798837^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77450901814412033149 50000000000000000000 11036455793798837 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11036455793798837/10000000000000000 : ℝ)) (X := (77450901814412033149/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(561831824333983/7472700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(26367998303603/415150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (74727/100000 : ℝ)) (alpha := (561831824333983/7472700000000000 : ℝ)) (beta := (26367998303603/415150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (74727/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(561831824333983/7472700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(26367998303603/415150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (85531/100000 : ℝ) ^ (71/16 : ℝ) ≤ (9996046031974346127/20000000000000000000 : ℝ) := by
    have hpowers : (85531/100000 : ℝ)^71 ≤ (9996046031974346127/20000000000000000000 : ℝ)^16 := by
      have hnat : (85531 : ℕ)^71*20000000000000000000^16 ≤ 9996046031974346127^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85531 100000 9996046031974346127 20000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85531/100000 : ℝ)) (X := (9996046031974346127/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (29996046031974346127/20000000000000000000 : ℝ) ≤ (5478222176825549/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (29996046031974346127/20000000000000000000 : ℝ)^16 ≤ (5478222176825549/5000000000000000 : ℝ)^71 := by
      have hnat : (29996046031974346127 : ℕ)^16*5000000000000000^71 ≤ 5478222176825549^71*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29996046031974346127 20000000000000000000 5478222176825549 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5478222176825549/5000000000000000 : ℝ)) (X := (29996046031974346127/20000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (19996046031974346127/10000000000000000000 : ℝ) ≤ (2922526135706509/2500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (19996046031974346127/10000000000000000000 : ℝ)^16 ≤ (2922526135706509/2500000000000000 : ℝ)^71 := by
      have hnat : (19996046031974346127 : ℕ)^16*2500000000000000^71 ≤ 2922526135706509^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19996046031974346127 10000000000000000000 2922526135706509 2500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2922526135706509/2500000000000000 : ℝ)) (X := (19996046031974346127/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(478222176825549/4276550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(366830094587469/4276550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (85531/100000 : ℝ)) (alpha := (478222176825549/4276550000000000 : ℝ)) (beta := (366830094587469/4276550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (85531/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(478222176825549/4276550000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(366830094587469/4276550000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8081/10000 : ℝ) ^ (71/16 : ℝ) ≤ (7769738582289674121/20000000000000000000 : ℝ) := by
    have hpowers : (8081/10000 : ℝ)^71 ≤ (7769738582289674121/20000000000000000000 : ℝ)^16 := by
      have hnat : (8081 : ℕ)^71*20000000000000000000^16 ≤ 7769738582289674121^16*10000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8081 10000 7769738582289674121 20000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8081/10000 : ℝ)) (X := (7769738582289674121/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (27769738582289674121/20000000000000000000 : ℝ) ≤ (10767678868337601/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (27769738582289674121/20000000000000000000 : ℝ)^16 ≤ (10767678868337601/10000000000000000 : ℝ)^71 := by
      have hnat : (27769738582289674121 : ℕ)^16*10000000000000000^71 ≤ 10767678868337601^71*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27769738582289674121 20000000000000000000 10767678868337601 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10767678868337601/10000000000000000 : ℝ)) (X := (27769738582289674121/20000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (17769738582289674121/10000000000000000000 : ℝ) ≤ (1138324673967309/1000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (17769738582289674121/10000000000000000000 : ℝ)^16 ≤ (1138324673967309/1000000000000000 : ℝ)^71 := by
      have hnat : (17769738582289674121 : ℕ)^16*1000000000000000^71 ≤ 1138324673967309^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17769738582289674121 10000000000000000000 1138324673967309 1000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1138324673967309/1000000000000000 : ℝ)) (X := (17769738582289674121/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(767678868337601/8081000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(615567871335489/8081000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (8081/10000 : ℝ)) (alpha := (767678868337601/8081000000000000 : ℝ)) (beta := (615567871335489/8081000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8081/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(767678868337601/8081000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(615567871335489/8081000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-230475543/2500000000 : ℝ)*X 0 0+(-642355903/1000000000 : ℝ)*X 0 1+(956357193/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5279459539/10000000000 : ℝ)*X 2 0+(-1934014881/5000000000 : ℝ)*X 2 1+(-890592491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2794251181/10000000000 : ℝ)*X 0 0+(-143653231/625000000 : ℝ)*X 0 1+(7194755241/10000000000 : ℝ)*X 0 2+(2794251181/10000000000 : ℝ)*X 1 0+(-143653231/625000000 : ℝ)*X 1 1+(7194755241/10000000000 : ℝ)*X 1 2+(2794251181/10000000000 : ℝ)*X 2 0+(-143653231/625000000 : ℝ)*X 2 1+(7194755241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-206677149/5000000000 : ℝ)*X 0 0+(-3714651177/5000000000 : ℝ)*X 0 1+(98237571/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((167726637/250000000 : ℝ)*X 1 0+(2897031467/10000000000 : ℝ)*X 1 1+(2838321179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1081991981/2000000000 : ℝ)*X 2 0+(-3741861989/10000000000 : ℝ)*X 2 1+(-3544383437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((10968683/100000000 : ℝ)*X 0 0+(-556959/8000000 : ℝ)*X 0 1+(1160749271/1250000000 : ℝ)*X 0 2+(10968683/100000000 : ℝ)*X 1 0+(-556959/8000000 : ℝ)*X 1 1+(1160749271/1250000000 : ℝ)*X 1 2+(10968683/100000000 : ℝ)*X 2 0+(-556959/8000000 : ℝ)*X 2 1+(1160749271/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-42976781/2500000000 : ℝ)*X 0 0+(-6112822663/10000000000 : ℝ)*X 0 1+(549895367/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1907705543/2500000000 : ℝ)*X 1 0+(238852381/1000000000 : ℝ)*X 1 1+(526647941/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3003820377/5000000000 : ℝ)*X 2 0+(-234015641/625000000 : ℝ)*X 2 1+(-283585369/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((128583533/1000000000 : ℝ)*X 0 0+(-1067166747/10000000000 : ℝ)*X 0 1+(8990537901/10000000000 : ℝ)*X 0 2+(128583533/1000000000 : ℝ)*X 1 0+(-1067166747/10000000000 : ℝ)*X 1 1+(8990537901/10000000000 : ℝ)*X 1 2+(128583533/1000000000 : ℝ)*X 2 0+(-1067166747/10000000000 : ℝ)*X 2 1+(8990537901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-209207927/10000000000 : ℝ)*X 0 0+(-7321757739/10000000000 : ℝ)*X 0 1+(2077488447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7828333413/10000000000 : ℝ)*X 1 0+(2205492969/10000000000 : ℝ)*X 1 1+(2007166537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4630647263/10000000000 : ℝ)*X 2 0+(-4433401647/10000000000 : ℝ)*X 2 1+(-3684118233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((77959081/200000000 : ℝ)*X 0 0+(-117768827/1250000000 : ℝ)*X 0 1+(7189090103/10000000000 : ℝ)*X 0 2+(77959081/200000000 : ℝ)*X 1 0+(-117768827/1250000000 : ℝ)*X 1 1+(7189090103/10000000000 : ℝ)*X 1 2+(77959081/200000000 : ℝ)*X 2 0+(-117768827/1250000000 : ℝ)*X 2 1+(7189090103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311075_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((36661/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36661/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1637888068671118606113615741/172794002750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1320249/1000000000000 : ℝ)*(base19) + (200465876401/500000000000 : ℝ)*(base40) + (1747493/1000000000000 : ℝ)*(base49) + (2563/6250000000 : ℝ)*(base54) + (368107/125000000000 : ℝ)*(base60) + (968136535737/250000000000 : ℝ)*(major_s1_0) + (968136535737/250000000000 : ℝ)*(major_s1_1) + (968136433217/250000000000 : ℝ)*(major_s1_2) + (444935683/1000000000000 : ℝ)*(sp_s1_2) + (5388727810121/1000000000000 : ℝ)*(sp_s1_7) + (673597394287/125000000000 : ℝ)*(sp_s1_8) + (2694167564391/500000000000 : ℝ)*(sp_s1_9) + (589077060413/250000000000 : ℝ)*(sp_s1_13) + (6583053/125000000000 : ℝ)*(sp_s1_21) + (589077162933/250000000000 : ℝ)*(f.failure) + (1077756094909/200000000000 : ℝ)*(f.sum) + (53273718953089364717/172794002750000000000000000000000 : ℝ)*base63 + (863178423731137/2020250000000000000000000000 : ℝ)*base65 + (361905433144377/1069137500000000000000000000 : ℝ)*base66 + (994235499790417/2020250000000000000000000000 : ℝ)*base69 + (3193912075532385751/16774135750000000000000000000000 : ℝ)*base71 + (43089836236539/103787500000000000000000000 : ℝ)*base72 + (151278412034603/4276550000000000000000000000 : ℝ)*base75 + (49407581621451/207575000000000000000000000 : ℝ)*base76 + (296647322553320857/3550819465000000000000000000000 : ℝ)*base79 + (3171/6250000000000000 : ℝ)*base87 + (3171/6250000000000000 : ℝ)*base89 + (3171/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-57643/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-57643/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1198957301473560937926093143321/93567952489125000000000000000000000 : ℝ) := by norm_num
    linear_combination (6320759/1000000000000 : ℝ)*(base13) + (1986149/500000000000 : ℝ)*(base21) + (278581358983/250000000000 : ℝ)*(base40) + (756561/125000000000 : ℝ)*(base49) + (225011387357/1000000000000 : ℝ)*(base60) + (311847134771/62500000000 : ℝ)*(major_s1_0) + (311847134771/62500000000 : ℝ)*(major_s1_1) + (311847134771/62500000000 : ℝ)*(major_s1_2) + (15828953/62500000000 : ℝ)*(sp_s1_13) + (694312882761/100000000000 : ℝ)*(sp_s1_14) + (6942656981829/1000000000000 : ℝ)*(sp_s1_15) + (6943131176071/1000000000000 : ℝ)*(sp_s1_16) + (3035715629793/1000000000000 : ℝ)*(sp_s1_20) + (23908327/50000000000 : ℝ)*(sp_s1_22) + (3035968893041/1000000000000 : ℝ)*(f.failure) + (6943135148369/1000000000000 : ℝ)*(f.sum) + (71390471115242303133/86397001375000000000000000000000 : ℝ)*base62 + (1716310505980051/2020250000000000000000000000 : ℝ)*base64 + (4044365601778129/4276550000000000000000000000 : ℝ)*base67 + (65003524917017/1010125000000000000000000000 : ℝ)*base69 + (1602932022045902359/6563792250000000000000000000000 : ℝ)*base70 + (8913449407031/18050000000000000000000000 : ℝ)*base73 + (9520074073731/267284375000000000000000000 : ℝ)*base75 + (37039546071457/162450000000000000000000000 : ℝ)*base76 + (12514500432790059/308766910000000000000000000000 : ℝ)*base79 + (24433/25000000000000000 : ℝ)*base86 + (24433/25000000000000000 : ℝ)*base88 + (24433/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20779/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8761689622247137740511707521979/1434708604833250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2880741/1000000000000 : ℝ)*(base22) + (135283724277/125000000000 : ℝ)*(base40) + (70568531137/500000000000 : ℝ)*(base49) + (269957340913/62500000000 : ℝ)*(major_s1_0) + (269957340913/62500000000 : ℝ)*(major_s1_1) + (269957340913/62500000000 : ℝ)*(major_s1_2) + (7868903/250000000000 : ℝ)*(sp_s1_0) + (17037691/1000000000000 : ℝ)*(sp_s1_6) + (586677/3906250000 : ℝ)*(sp_s1_7) + (3427771/250000000000 : ℝ)*(sp_s1_16) + (3005148933289/500000000000 : ℝ)*(sp_s1_21) + (3005239765751/500000000000 : ℝ)*(sp_s1_22) + (1502615734919/250000000000 : ℝ)*(sp_s1_23) + (2628136304369/1000000000000 : ℝ)*(sp_s1_27) + (131407667103/50000000000 : ℝ)*(f.failure) + (3005239765751/500000000000 : ℝ)*(f.sum) + (13955763947435858227/172794002750000000000000000000000 : ℝ)*base63 + (114312652056961/1010125000000000000000000000 : ℝ)*base65 + (644040675439679/2138275000000000000000000000 : ℝ)*base66 + (246518882411323/2020250000000000000000000000 : ℝ)*base68 + (29521055529632221177/75483610875000000000000000000000 : ℝ)*base71 + (33068838281507/51893750000000000000000000 : ℝ)*base72 + (1853725649250373/4276550000000000000000000000 : ℝ)*base75 + (261672781280377/934087500000000000000000000 : ℝ)*base76 + (2921751421887350623/3550819465000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (961/1250000000000000 : ℝ)*base87 + (961/1250000000000000 : ℝ)*base89 + (961/1250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((74727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-85531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-85531/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8081/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8081/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((36661/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36661/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-57643/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-57643/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20779/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311075_s1 p hpa hpb X hX hprev0

#print axioms solution
