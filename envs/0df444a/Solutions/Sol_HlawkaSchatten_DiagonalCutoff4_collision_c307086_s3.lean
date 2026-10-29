-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307086_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:52.599461+00:00
-- url     : https://prove2.me/submissions/da94791d-119e-4a4d-8b82-d8095b8d020e

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
theorem collision_support_c307086_s3_s3_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-202838729/2500000000 : ℝ)*x 0 + (-5863843433/10000000000 : ℝ)*x 1 + (1391929369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202838729/2500000000 : ℝ)^17 ≤ (374613520539/10000000000000 : ℝ)^13 := by
    have hnat : (202838729 : ℕ)^17*10000000000000^13 ≤ 374613520539^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202838729 2500000000 374613520539 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5863843433/10000000000 : ℝ)^17 ≤ (49756962835831/100000000000000 : ℝ)^13 := by
    have hnat : (5863843433 : ℕ)^17*100000000000000^13 ≤ 49756962835831^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5863843433 10000000000 49756962835831 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1391929369/2500000000 : ℝ)^17 ≤ (23248450978609/50000000000000 : ℝ)^13 := by
    have hnat : (1391929369 : ℕ)^17*50000000000000^13 ≤ 23248450978609^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391929369 2500000000 23248450978609 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202838729/2500000000 : ℝ), (-5863843433/10000000000 : ℝ), (1391929369/2500000000 : ℝ)] ![(374613520539/10000000000000 : ℝ), (49756962835831/100000000000000 : ℝ), (23248450978609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202838729/2500000000 : ℝ)|^17 ≤ (374613520539/10000000000000 : ℝ)^13
        have hw : |(-202838729/2500000000 : ℝ)|=(202838729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5863843433/10000000000 : ℝ)|^17 ≤ (49756962835831/100000000000000 : ℝ)^13
        have hw : |(-5863843433/10000000000 : ℝ)|=(5863843433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1391929369/2500000000 : ℝ)|^17 ≤ (23248450978609/50000000000000 : ℝ)^13
        have hw : |(1391929369/2500000000 : ℝ)|=(1391929369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (284362443/500000000 : ℝ)*x 0 + (-3705794739/10000000000 : ℝ)*x 1 + (-3452442651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284362443/500000000 : ℝ)^17 ≤ (11951641104507/25000000000000 : ℝ)^13 := by
    have hnat : (284362443 : ℕ)^17*25000000000000^13 ≤ 11951641104507^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284362443 500000000 11951641104507 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3705794739/10000000000 : ℝ)^17 ≤ (27304200936057/100000000000000 : ℝ)^13 := by
    have hnat : (3705794739 : ℕ)^17*100000000000000^13 ≤ 27304200936057^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705794739 10000000000 27304200936057 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3452442651/10000000000 : ℝ)^17 ≤ (24889234633051/100000000000000 : ℝ)^13 := by
    have hnat : (3452442651 : ℕ)^17*100000000000000^13 ≤ 24889234633051^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3452442651 10000000000 24889234633051 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(284362443/500000000 : ℝ), (-3705794739/10000000000 : ℝ), (-3452442651/10000000000 : ℝ)] ![(11951641104507/25000000000000 : ℝ), (27304200936057/100000000000000 : ℝ), (24889234633051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(284362443/500000000 : ℝ)|^17 ≤ (11951641104507/25000000000000 : ℝ)^13
        have hw : |(284362443/500000000 : ℝ)|=(284362443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3705794739/10000000000 : ℝ)|^17 ≤ (27304200936057/100000000000000 : ℝ)^13
        have hw : |(-3705794739/10000000000 : ℝ)|=(3705794739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3452442651/10000000000 : ℝ)|^17 ≤ (24889234633051/100000000000000 : ℝ)^13
        have hw : |(-3452442651/10000000000 : ℝ)|=(3452442651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-304545663/5000000000 : ℝ)*x 0 + (-6799829511/10000000000 : ℝ)*x 1 + (4678697403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304545663/5000000000 : ℝ)^17 ≤ (514954121119/20000000000000 : ℝ)^13 := by
    have hnat : (304545663 : ℕ)^17*20000000000000^13 ≤ 514954121119^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304545663 5000000000 514954121119 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6799829511/10000000000 : ℝ)^17 ≤ (12077831046723/20000000000000 : ℝ)^13 := by
    have hnat : (6799829511 : ℕ)^17*20000000000000^13 ≤ 12077831046723^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6799829511 10000000000 12077831046723 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4678697403/10000000000 : ℝ)^17 ≤ (18518037075573/50000000000000 : ℝ)^13 := by
    have hnat : (4678697403 : ℕ)^17*50000000000000^13 ≤ 18518037075573^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4678697403 10000000000 18518037075573 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-304545663/5000000000 : ℝ), (-6799829511/10000000000 : ℝ), (4678697403/10000000000 : ℝ)] ![(514954121119/20000000000000 : ℝ), (12077831046723/20000000000000 : ℝ), (18518037075573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-304545663/5000000000 : ℝ)|^17 ≤ (514954121119/20000000000000 : ℝ)^13
        have hw : |(-304545663/5000000000 : ℝ)|=(304545663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6799829511/10000000000 : ℝ)|^17 ≤ (12077831046723/20000000000000 : ℝ)^13
        have hw : |(-6799829511/10000000000 : ℝ)|=(6799829511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4678697403/10000000000 : ℝ)|^17 ≤ (18518037075573/50000000000000 : ℝ)^13
        have hw : |(4678697403/10000000000 : ℝ)|=(4678697403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5955663699/10000000000 : ℝ)*x 0 + (3453495611/10000000000 : ℝ)*x 1 + (27137371/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5955663699/10000000000 : ℝ)^17 ≤ (10155654216101/20000000000000 : ℝ)^13 := by
    have hnat : (5955663699 : ℕ)^17*20000000000000^13 ≤ 10155654216101^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5955663699 10000000000 10155654216101 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3453495611/10000000000 : ℝ)^17 ≤ (12449580872129/50000000000000 : ℝ)^13 := by
    have hnat : (3453495611 : ℕ)^17*50000000000000^13 ≤ 12449580872129^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3453495611 10000000000 12449580872129 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27137371/80000000 : ℝ)^17 ≤ (12161283577921/50000000000000 : ℝ)^13 := by
    have hnat : (27137371 : ℕ)^17*50000000000000^13 ≤ 12161283577921^13*80000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27137371 80000000 12161283577921 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5955663699/10000000000 : ℝ), (3453495611/10000000000 : ℝ), (27137371/80000000 : ℝ)] ![(10155654216101/20000000000000 : ℝ), (12449580872129/50000000000000 : ℝ), (12161283577921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5955663699/10000000000 : ℝ)|^17 ≤ (10155654216101/20000000000000 : ℝ)^13
        have hw : |(5955663699/10000000000 : ℝ)|=(5955663699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3453495611/10000000000 : ℝ)|^17 ≤ (12449580872129/50000000000000 : ℝ)^13
        have hw : |(3453495611/10000000000 : ℝ)|=(3453495611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27137371/80000000 : ℝ)|^17 ≤ (12161283577921/50000000000000 : ℝ)^13
        have hw : |(27137371/80000000 : ℝ)|=(27137371/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2974454467/5000000000 : ℝ)*x 0 + (-173607463/500000000 : ℝ)*x 1 + (-1690712223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2974454467/5000000000 : ℝ)^17 ≤ (25351486166607/50000000000000 : ℝ)^13 := by
    have hnat : (2974454467 : ℕ)^17*50000000000000^13 ≤ 25351486166607^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974454467 5000000000 25351486166607 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173607463/500000000 : ℝ)^17 ≤ (12537589547499/50000000000000 : ℝ)^13 := by
    have hnat : (173607463 : ℕ)^17*50000000000000^13 ≤ 12537589547499^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173607463 500000000 12537589547499 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690712223/5000000000 : ℝ)^17 ≤ (6055462138439/25000000000000 : ℝ)^13 := by
    have hnat : (1690712223 : ℕ)^17*25000000000000^13 ≤ 6055462138439^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690712223 5000000000 6055462138439 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2974454467/5000000000 : ℝ), (-173607463/500000000 : ℝ), (-1690712223/5000000000 : ℝ)] ![(25351486166607/50000000000000 : ℝ), (12537589547499/50000000000000 : ℝ), (6055462138439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2974454467/5000000000 : ℝ)|^17 ≤ (25351486166607/50000000000000 : ℝ)^13
        have hw : |(2974454467/5000000000 : ℝ)|=(2974454467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173607463/500000000 : ℝ)|^17 ≤ (12537589547499/50000000000000 : ℝ)^13
        have hw : |(-173607463/500000000 : ℝ)|=(173607463/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1690712223/5000000000 : ℝ)|^17 ≤ (6055462138439/25000000000000 : ℝ)^13
        have hw : |(-1690712223/5000000000 : ℝ)|=(1690712223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (137162407/400000000 : ℝ)*x 0 + (-428624599/2000000000 : ℝ)*x 1 + (6937172989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137162407/400000000 : ℝ)^17 ≤ (12334514690759/50000000000000 : ℝ)^13 := by
    have hnat : (137162407 : ℕ)^17*50000000000000^13 ≤ 12334514690759^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137162407 400000000 12334514690759 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428624599/2000000000 : ℝ)^17 ≤ (13341830946493/100000000000000 : ℝ)^13 := by
    have hnat : (428624599 : ℕ)^17*100000000000000^13 ≤ 13341830946493^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428624599 2000000000 13341830946493 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6937172989/10000000000 : ℝ)^17 ≤ (7748642457491/12500000000000 : ℝ)^13 := by
    have hnat : (6937172989 : ℕ)^17*12500000000000^13 ≤ 7748642457491^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6937172989 10000000000 7748642457491 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(137162407/400000000 : ℝ), (-428624599/2000000000 : ℝ), (6937172989/10000000000 : ℝ)] ![(12334514690759/50000000000000 : ℝ), (13341830946493/100000000000000 : ℝ), (7748642457491/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(137162407/400000000 : ℝ)|^17 ≤ (12334514690759/50000000000000 : ℝ)^13
        have hw : |(137162407/400000000 : ℝ)|=(137162407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428624599/2000000000 : ℝ)|^17 ≤ (13341830946493/100000000000000 : ℝ)^13
        have hw : |(-428624599/2000000000 : ℝ)|=(428624599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6937172989/10000000000 : ℝ)|^17 ≤ (7748642457491/12500000000000 : ℝ)^13
        have hw : |(6937172989/10000000000 : ℝ)|=(6937172989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-100483949/5000000000 : ℝ)*x 0 + (-5607523747/10000000000 : ℝ)*x 1 + (6106269849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100483949/5000000000 : ℝ)^17 ≤ (603965074641/100000000000000 : ℝ)^13 := by
    have hnat : (100483949 : ℕ)^17*100000000000000^13 ≤ 603965074641^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100483949 5000000000 603965074641 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607523747/10000000000 : ℝ)^17 ≤ (23466046793403/50000000000000 : ℝ)^13 := by
    have hnat : (5607523747 : ℕ)^17*50000000000000^13 ≤ 23466046793403^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607523747 10000000000 23466046793403 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6106269849/10000000000 : ℝ)^17 ≤ (52463941327303/100000000000000 : ℝ)^13 := by
    have hnat : (6106269849 : ℕ)^17*100000000000000^13 ≤ 52463941327303^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6106269849 10000000000 52463941327303 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100483949/5000000000 : ℝ), (-5607523747/10000000000 : ℝ), (6106269849/10000000000 : ℝ)] ![(603965074641/100000000000000 : ℝ), (23466046793403/50000000000000 : ℝ), (52463941327303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100483949/5000000000 : ℝ)|^17 ≤ (603965074641/100000000000000 : ℝ)^13
        have hw : |(-100483949/5000000000 : ℝ)|=(100483949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5607523747/10000000000 : ℝ)|^17 ≤ (23466046793403/50000000000000 : ℝ)^13
        have hw : |(-5607523747/10000000000 : ℝ)|=(5607523747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6106269849/10000000000 : ℝ)|^17 ≤ (52463941327303/100000000000000 : ℝ)^13
        have hw : |(6106269849/10000000000 : ℝ)|=(6106269849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6664816941/10000000000 : ℝ)*x 0 + (3265615699/10000000000 : ℝ)*x 1 + (1349111823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6664816941/10000000000 : ℝ)^17 ≤ (11765197269121/20000000000000 : ℝ)^13 := by
    have hnat : (6664816941 : ℕ)^17*20000000000000^13 ≤ 11765197269121^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6664816941 10000000000 11765197269121 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3265615699/10000000000 : ℝ)^17 ≤ (23142798154033/100000000000000 : ℝ)^13 := by
    have hnat : (3265615699 : ℕ)^17*100000000000000^13 ≤ 23142798154033^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3265615699 10000000000 23142798154033 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349111823/5000000000 : ℝ)^17 ≤ (18031215488237/100000000000000 : ℝ)^13 := by
    have hnat : (1349111823 : ℕ)^17*100000000000000^13 ≤ 18031215488237^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349111823 5000000000 18031215488237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6664816941/10000000000 : ℝ), (3265615699/10000000000 : ℝ), (1349111823/5000000000 : ℝ)] ![(11765197269121/20000000000000 : ℝ), (23142798154033/100000000000000 : ℝ), (18031215488237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6664816941/10000000000 : ℝ)|^17 ≤ (11765197269121/20000000000000 : ℝ)^13
        have hw : |(6664816941/10000000000 : ℝ)|=(6664816941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3265615699/10000000000 : ℝ)|^17 ≤ (23142798154033/100000000000000 : ℝ)^13
        have hw : |(3265615699/10000000000 : ℝ)|=(3265615699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349111823/5000000000 : ℝ)|^17 ≤ (18031215488237/100000000000000 : ℝ)^13
        have hw : |(1349111823/5000000000 : ℝ)|=(1349111823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6177369409/10000000000 : ℝ)*x 0 + (-91924097/250000000 : ℝ)*x 1 + (-1444098057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6177369409/10000000000 : ℝ)^17 ≤ (53264204071201/100000000000000 : ℝ)^13 := by
    have hnat : (6177369409 : ℕ)^17*100000000000000^13 ≤ 53264204071201^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6177369409 10000000000 53264204071201 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91924097/250000000 : ℝ)^17 ≤ (13513373720397/50000000000000 : ℝ)^13 := by
    have hnat : (91924097 : ℕ)^17*50000000000000^13 ≤ 13513373720397^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91924097 250000000 13513373720397 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444098057/5000000000 : ℝ)^17 ≤ (9854524235431/50000000000000 : ℝ)^13 := by
    have hnat : (1444098057 : ℕ)^17*50000000000000^13 ≤ 9854524235431^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444098057 5000000000 9854524235431 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6177369409/10000000000 : ℝ), (-91924097/250000000 : ℝ), (-1444098057/5000000000 : ℝ)] ![(53264204071201/100000000000000 : ℝ), (13513373720397/50000000000000 : ℝ), (9854524235431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6177369409/10000000000 : ℝ)|^17 ≤ (53264204071201/100000000000000 : ℝ)^13
        have hw : |(6177369409/10000000000 : ℝ)|=(6177369409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91924097/250000000 : ℝ)|^17 ≤ (13513373720397/50000000000000 : ℝ)^13
        have hw : |(-91924097/250000000 : ℝ)|=(91924097/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1444098057/5000000000 : ℝ)|^17 ≤ (9854524235431/50000000000000 : ℝ)^13
        have hw : |(-1444098057/5000000000 : ℝ)|=(1444098057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3582107369/10000000000 : ℝ)*x 0 + (-6664593/25000000 : ℝ)*x 1 + (25117919/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3582107369/10000000000 : ℝ)^17 ≤ (5223726993651/20000000000000 : ℝ)^13 := by
    have hnat : (3582107369 : ℕ)^17*20000000000000^13 ≤ 5223726993651^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3582107369 10000000000 5223726993651 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6664593/25000000 : ℝ)^17 ≤ (8874360175573/50000000000000 : ℝ)^13 := by
    have hnat : (6664593 : ℕ)^17*50000000000000^13 ≤ 8874360175573^13*25000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6664593 25000000 8874360175573 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25117919/39062500 : ℝ)^17 ≤ (28066322330461/50000000000000 : ℝ)^13 := by
    have hnat : (25117919 : ℕ)^17*50000000000000^13 ≤ 28066322330461^13*39062500^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25117919 39062500 28066322330461 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3582107369/10000000000 : ℝ), (-6664593/25000000 : ℝ), (25117919/39062500 : ℝ)] ![(5223726993651/20000000000000 : ℝ), (8874360175573/50000000000000 : ℝ), (28066322330461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3582107369/10000000000 : ℝ)|^17 ≤ (5223726993651/20000000000000 : ℝ)^13
        have hw : |(3582107369/10000000000 : ℝ)|=(3582107369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6664593/25000000 : ℝ)|^17 ≤ (8874360175573/50000000000000 : ℝ)^13
        have hw : |(-6664593/25000000 : ℝ)|=(6664593/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25117919/39062500 : ℝ)|^17 ≤ (28066322330461/50000000000000 : ℝ)^13
        have hw : |(25117919/39062500 : ℝ)|=(25117919/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-147543319/10000000000 : ℝ)*x 0 + (-404046113/625000000 : ℝ)*x 1 + (2625529759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (147543319/10000000000 : ℝ)^17 ≤ (40319039641/10000000000000 : ℝ)^13 := by
    have hnat : (147543319 : ℕ)^17*10000000000000^13 ≤ 40319039641^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147543319 10000000000 40319039641 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404046113/625000000 : ℝ)^17 ≤ (28263692157649/50000000000000 : ℝ)^13 := by
    have hnat : (404046113 : ℕ)^17*50000000000000^13 ≤ 28263692157649^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404046113 625000000 28263692157649 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2625529759/5000000000 : ℝ)^17 ≤ (43069425269119/100000000000000 : ℝ)^13 := by
    have hnat : (2625529759 : ℕ)^17*100000000000000^13 ≤ 43069425269119^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625529759 5000000000 43069425269119 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-147543319/10000000000 : ℝ), (-404046113/625000000 : ℝ), (2625529759/5000000000 : ℝ)] ![(40319039641/10000000000000 : ℝ), (28263692157649/50000000000000 : ℝ), (43069425269119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-147543319/10000000000 : ℝ)|^17 ≤ (40319039641/10000000000000 : ℝ)^13
        have hw : |(-147543319/10000000000 : ℝ)|=(147543319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404046113/625000000 : ℝ)|^17 ≤ (28263692157649/50000000000000 : ℝ)^13
        have hw : |(-404046113/625000000 : ℝ)|=(404046113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2625529759/5000000000 : ℝ)|^17 ≤ (43069425269119/100000000000000 : ℝ)^13
        have hw : |(2625529759/5000000000 : ℝ)|=(2625529759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (335912111/500000000 : ℝ)*x 0 + (3058310889/10000000000 : ℝ)*x 1 + (568807899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335912111/500000000 : ℝ)^17 ≤ (14860846943723/25000000000000 : ℝ)^13 := by
    have hnat : (335912111 : ℕ)^17*25000000000000^13 ≤ 14860846943723^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335912111 500000000 14860846943723 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3058310889/10000000000 : ℝ)^17 ≤ (21240673669259/100000000000000 : ℝ)^13 := by
    have hnat : (3058310889 : ℕ)^17*100000000000000^13 ≤ 21240673669259^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3058310889 10000000000 21240673669259 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568807899/2000000000 : ℝ)^17 ≤ (9657969269319/50000000000000 : ℝ)^13 := by
    have hnat : (568807899 : ℕ)^17*50000000000000^13 ≤ 9657969269319^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568807899 2000000000 9657969269319 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335912111/500000000 : ℝ), (3058310889/10000000000 : ℝ), (568807899/2000000000 : ℝ)] ![(14860846943723/25000000000000 : ℝ), (21240673669259/100000000000000 : ℝ), (9657969269319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335912111/500000000 : ℝ)|^17 ≤ (14860846943723/25000000000000 : ℝ)^13
        have hw : |(335912111/500000000 : ℝ)|=(335912111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3058310889/10000000000 : ℝ)|^17 ≤ (21240673669259/100000000000000 : ℝ)^13
        have hw : |(3058310889/10000000000 : ℝ)|=(3058310889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568807899/2000000000 : ℝ)|^17 ≤ (9657969269319/50000000000000 : ℝ)^13
        have hw : |(568807899/2000000000 : ℝ)|=(568807899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (21361417/39062500 : ℝ)*x 0 + (-3867333763/10000000000 : ℝ)*x 1 + (-35394267/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21361417/39062500 : ℝ)^17 ≤ (45416602843561/100000000000000 : ℝ)^13 := by
    have hnat : (21361417 : ℕ)^17*100000000000000^13 ≤ 45416602843561^13*39062500^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21361417 39062500 45416602843561 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3867333763/10000000000 : ℝ)^17 ≤ (4511089261/15625000000 : ℝ)^13 := by
    have hnat : (3867333763 : ℕ)^17*15625000000^13 ≤ 4511089261^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867333763 10000000000 4511089261 15625000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35394267/100000000 : ℝ)^17 ≤ (12856212939583/50000000000000 : ℝ)^13 := by
    have hnat : (35394267 : ℕ)^17*50000000000000^13 ≤ 12856212939583^13*100000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35394267 100000000 12856212939583 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21361417/39062500 : ℝ), (-3867333763/10000000000 : ℝ), (-35394267/100000000 : ℝ)] ![(45416602843561/100000000000000 : ℝ), (4511089261/15625000000 : ℝ), (12856212939583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21361417/39062500 : ℝ)|^17 ≤ (45416602843561/100000000000000 : ℝ)^13
        have hw : |(21361417/39062500 : ℝ)|=(21361417/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3867333763/10000000000 : ℝ)|^17 ≤ (4511089261/15625000000 : ℝ)^13
        have hw : |(-3867333763/10000000000 : ℝ)|=(3867333763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35394267/100000000 : ℝ)|^17 ≤ (12856212939583/50000000000000 : ℝ)^13
        have hw : |(-35394267/100000000 : ℝ)|=(35394267/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s3_s3_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (507703723/1000000000 : ℝ)*x 0 + (-2849819009/10000000000 : ℝ)*x 1 + (4907315323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507703723/1000000000 : ℝ)^17 ≤ (8242499176339/20000000000000 : ℝ)^13 := by
    have hnat : (507703723 : ℕ)^17*20000000000000^13 ≤ 8242499176339^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507703723 1000000000 8242499176339 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2849819009/10000000000 : ℝ)^17 ≤ (3873457053309/20000000000000 : ℝ)^13 := by
    have hnat : (2849819009 : ℕ)^17*20000000000000^13 ≤ 3873457053309^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849819009 10000000000 3873457053309 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4907315323/10000000000 : ℝ)^17 ≤ (76992614911/195312500000 : ℝ)^13 := by
    have hnat : (4907315323 : ℕ)^17*195312500000^13 ≤ 76992614911^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4907315323 10000000000 76992614911 195312500000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(507703723/1000000000 : ℝ), (-2849819009/10000000000 : ℝ), (4907315323/10000000000 : ℝ)] ![(8242499176339/20000000000000 : ℝ), (3873457053309/20000000000000 : ℝ), (76992614911/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(507703723/1000000000 : ℝ)|^17 ≤ (8242499176339/20000000000000 : ℝ)^13
        have hw : |(507703723/1000000000 : ℝ)|=(507703723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2849819009/10000000000 : ℝ)|^17 ≤ (3873457053309/20000000000000 : ℝ)^13
        have hw : |(-2849819009/10000000000 : ℝ)|=(2849819009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4907315323/10000000000 : ℝ)|^17 ≤ (76992614911/195312500000 : ℝ)^13
        have hw : |(4907315323/10000000000 : ℝ)|=(4907315323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307086_s3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((1536/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1536/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-73807/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-73807/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1749/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1749/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8133/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8133/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7813/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7813/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7847/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7847/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (1536/3125 : ℝ) ^ (135/32 : ℝ) ≤ (4996770607602787091/100000000000000000000 : ℝ) := by
    have hpowers : (1536/3125 : ℝ)^135 ≤ (4996770607602787091/100000000000000000000 : ℝ)^32 := by
      have hnat : (1536 : ℕ)^135*100000000000000000000^32 ≤ 4996770607602787091^32*3125^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1536 3125 4996770607602787091 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1536/3125 : ℝ)) (X := (4996770607602787091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (104996770607602787091/100000000000000000000 : ℝ) ≤ (5058124173837961/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (104996770607602787091/100000000000000000000 : ℝ)^32 ≤ (5058124173837961/5000000000000000 : ℝ)^135 := by
      have hnat : (104996770607602787091 : ℕ)^32*5000000000000000^135 ≤ 5058124173837961^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104996770607602787091 100000000000000000000 5058124173837961 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058124173837961/5000000000000000 : ℝ)) (X := (104996770607602787091/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (54996770607602787091/50000000000000000000 : ℝ) ≤ (10228349392981639/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (54996770607602787091/50000000000000000000 : ℝ)^32 ≤ (10228349392981639/10000000000000000 : ℝ)^135 := by
      have hnat : (54996770607602787091 : ℕ)^32*10000000000000000^135 ≤ 10228349392981639^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54996770607602787091 50000000000000000000 10228349392981639 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10228349392981639/10000000000000000 : ℝ)) (X := (54996770607602787091/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(58124173837961/2457600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(112101045305717/4915200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1536/3125 : ℝ)) (alpha := (58124173837961/2457600000000000 : ℝ)) (beta := (112101045305717/4915200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1536/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(58124173837961/2457600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(112101045305717/4915200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (73807/100000 : ℝ) ^ (135/32 : ℝ) ≤ (5553497080076601223/20000000000000000000 : ℝ) := by
    have hpowers : (73807/100000 : ℝ)^135 ≤ (5553497080076601223/20000000000000000000 : ℝ)^32 := by
      have hnat : (73807 : ℕ)^135*20000000000000000000^32 ≤ 5553497080076601223^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73807 100000 5553497080076601223 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73807/100000 : ℝ)) (X := (5553497080076601223/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (25553497080076601223/20000000000000000000 : ℝ) ≤ (10598040232330621/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (25553497080076601223/20000000000000000000 : ℝ)^32 ≤ (10598040232330621/10000000000000000 : ℝ)^135 := by
      have hnat : (25553497080076601223 : ℕ)^32*10000000000000000^135 ≤ 10598040232330621^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25553497080076601223 20000000000000000000 10598040232330621 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10598040232330621/10000000000000000 : ℝ)) (X := (25553497080076601223/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (15553497080076601223/10000000000000000000 : ℝ) ≤ (11103767333382729/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (15553497080076601223/10000000000000000000 : ℝ)^32 ≤ (11103767333382729/10000000000000000 : ℝ)^135 := by
      have hnat : (15553497080076601223 : ℕ)^32*10000000000000000^135 ≤ 11103767333382729^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15553497080076601223 10000000000000000000 11103767333382729 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11103767333382729/10000000000000000 : ℝ)) (X := (15553497080076601223/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(598040232330621/7380700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(126431775263027/1845175000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (73807/100000 : ℝ)) (alpha := (598040232330621/7380700000000000 : ℝ)) (beta := (126431775263027/1845175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (73807/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(598040232330621/7380700000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(126431775263027/1845175000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (1749/2500 : ℝ) ^ (135/32 : ℝ) ≤ (22154405329483533107/100000000000000000000 : ℝ) := by
    have hpowers : (1749/2500 : ℝ)^135 ≤ (22154405329483533107/100000000000000000000 : ℝ)^32 := by
      have hnat : (1749 : ℕ)^135*100000000000000000000^32 ≤ 22154405329483533107^32*2500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1749 2500 22154405329483533107 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1749/2500 : ℝ)) (X := (22154405329483533107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (122154405329483533107/100000000000000000000 : ℝ) ≤ (5242889299119093/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (122154405329483533107/100000000000000000000 : ℝ)^32 ≤ (5242889299119093/5000000000000000 : ℝ)^135 := by
      have hnat : (122154405329483533107 : ℕ)^32*5000000000000000^135 ≤ 5242889299119093^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        122154405329483533107 100000000000000000000 5242889299119093 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5242889299119093/5000000000000000 : ℝ)) (X := (122154405329483533107/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (72154405329483533107/50000000000000000000 : ℝ) ≤ (5454165461874151/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (72154405329483533107/50000000000000000000 : ℝ)^32 ≤ (5454165461874151/5000000000000000 : ℝ)^135 := by
      have hnat : (72154405329483533107 : ℕ)^32*5000000000000000^135 ≤ 5454165461874151^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72154405329483533107 50000000000000000000 5454165461874151 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5454165461874151/5000000000000000 : ℝ)) (X := (72154405329483533107/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(22080845374463/318000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(105638081377529/1749000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1749/2500 : ℝ)) (alpha := (22080845374463/318000000000000 : ℝ)) (beta := (105638081377529/1749000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1749/2500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(22080845374463/318000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(105638081377529/1749000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-202838729/2500000000 : ℝ)*X 0 0+(-5863843433/10000000000 : ℝ)*X 0 1+(1391929369/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((284362443/500000000 : ℝ)*X 2 0+(-3705794739/10000000000 : ℝ)*X 2 1+(-3452442651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-304545663/5000000000 : ℝ)*X 0 0+(-6799829511/10000000000 : ℝ)*X 0 1+(4678697403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((5955663699/10000000000 : ℝ)*X 1 0+(3453495611/10000000000 : ℝ)*X 1 1+(27137371/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((2974454467/5000000000 : ℝ)*X 2 0+(-173607463/500000000 : ℝ)*X 2 1+(-1690712223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((137162407/400000000 : ℝ)*X 0 0+(-428624599/2000000000 : ℝ)*X 0 1+(6937172989/10000000000 : ℝ)*X 0 2+(137162407/400000000 : ℝ)*X 1 0+(-428624599/2000000000 : ℝ)*X 1 1+(6937172989/10000000000 : ℝ)*X 1 2+(137162407/400000000 : ℝ)*X 2 0+(-428624599/2000000000 : ℝ)*X 2 1+(6937172989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-100483949/5000000000 : ℝ)*X 0 0+(-5607523747/10000000000 : ℝ)*X 0 1+(6106269849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((6664816941/10000000000 : ℝ)*X 1 0+(3265615699/10000000000 : ℝ)*X 1 1+(1349111823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((6177369409/10000000000 : ℝ)*X 2 0+(-91924097/250000000 : ℝ)*X 2 1+(-1444098057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3582107369/10000000000 : ℝ)*X 0 0+(-6664593/25000000 : ℝ)*X 0 1+(25117919/39062500 : ℝ)*X 0 2+(3582107369/10000000000 : ℝ)*X 1 0+(-6664593/25000000 : ℝ)*X 1 1+(25117919/39062500 : ℝ)*X 1 2+(3582107369/10000000000 : ℝ)*X 2 0+(-6664593/25000000 : ℝ)*X 2 1+(25117919/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-147543319/10000000000 : ℝ)*X 0 0+(-404046113/625000000 : ℝ)*X 0 1+(2625529759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((335912111/500000000 : ℝ)*X 1 0+(3058310889/10000000000 : ℝ)*X 1 1+(568807899/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((21361417/39062500 : ℝ)*X 2 0+(-3867333763/10000000000 : ℝ)*X 2 1+(-35394267/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((507703723/1000000000 : ℝ)*X 0 0+(-2849819009/10000000000 : ℝ)*X 0 1+(4907315323/10000000000 : ℝ)*X 0 2+(507703723/1000000000 : ℝ)*X 1 0+(-2849819009/10000000000 : ℝ)*X 1 1+(4907315323/10000000000 : ℝ)*X 1 2+(507703723/1000000000 : ℝ)*X 2 0+(-2849819009/10000000000 : ℝ)*X 2 1+(4907315323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((8133/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8133/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (92961464741006529606750545841/8011307008000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92653274569/200000000000 : ℝ)*(base40) + (1023963/500000000000 : ℝ)*(base50) + (4988351/1000000000000 : ℝ)*(base60) + (3982605739313/1000000000000 : ℝ)*(major_s3_0) + (3982605739313/1000000000000 : ℝ)*(major_s3_1) + (3982605739313/1000000000000 : ℝ)*(major_s3_2) + (662403/1000000000000 : ℝ)*(sp_s3_0) + (147885247/500000000000 : ℝ)*(sp_s3_2) + (5403127933871/1000000000000 : ℝ)*(sp_s3_7) + (1080637922309/200000000000 : ℝ)*(sp_s3_8) + (135071556947/25000000000 : ℝ)*(sp_s3_9) + (1281008999573/500000000000 : ℝ)*(sp_s3_13) + (7890793/250000000000 : ℝ)*(sp_s3_16) + (61015271/1000000000000 : ℝ)*(sp_s3_21) + (1281008999573/500000000000 : ℝ)*(f.failure) + (1080637922309/200000000000 : ℝ)*(f.sum) + (16143061796396668153/23470626000000000000000000000000 : ℝ)*base63 + (680712251429377/1749000000000000000000000000 : ℝ)*base64 + (650738816906463/7380700000000000000000000000 : ℝ)*base67 + (220279232304919/318000000000000000000000000 : ℝ)*base69 + (4348556613209096203/7163904000000000000000000000000 : ℝ)*base71 + (657695240253541/4915200000000000000000000000 : ℝ)*base73 + (48319103534871/115323437500000000000000000 : ℝ)*base75 + (814842519997753/2457600000000000000000000000 : ℝ)*base77 + (178810509618551681237/362776166400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (3287/6250000000000000 : ℝ)*base86 + (3287/6250000000000000 : ℝ)*base88 + (3287/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-7813/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7813/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (843829887206781336585608877/60462694400000000000000000000000 : ℝ) := by norm_num
    linear_combination (1571177/250000000000 : ℝ)*(base39) + (301848801679/200000000000 : ℝ)*(base40) + (404906132681/1000000000000 : ℝ)*(base60) + (6208722424671/1000000000000 : ℝ)*(major_s3_0) + (6208722424671/1000000000000 : ℝ)*(major_s3_1) + (6208722424671/1000000000000 : ℝ)*(major_s3_2) + (7726289/200000000000 : ℝ)*(sp_s3_0) + (85720591/500000000000 : ℝ)*(sp_s3_13) + (8423318383879/1000000000000 : ℝ)*(sp_s3_14) + (8423090436463/1000000000000 : ℝ)*(sp_s3_15) + (2105839253831/250000000000 : ℝ)*(sp_s3_16) + (1996936714121/500000000000 : ℝ)*(sp_s3_20) + (133289431/500000000000 : ℝ)*(sp_s3_22) + (19156261/500000000000 : ℝ)*(sp_s3_27) + (1997041590973/500000000000 : ℝ)*(f.failure) + (2105839253831/250000000000 : ℝ)*(f.sum) + (844867889311690917/7823542000000000000000000000000 : ℝ)*base63 + (37090148861147/583000000000000000000000000 : ℝ)*base65 + (1107950564875881/7380700000000000000000000000 : ℝ)*base67 + (26089086169709/106000000000000000000000000 : ℝ)*base68 + (569087511860149833/2387968000000000000000000000000 : ℝ)*base70 + (61191537666169/1638400000000000000000000000 : ℝ)*base73 + (252965396315947/1845175000000000000000000000 : ℝ)*base75 + (418319857323363/819200000000000000000000000 : ℝ)*base76 + (5375779956507925847/120925388800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (2613/6250000000000000 : ℝ)*base87 + (2613/6250000000000000 : ℝ)*base89 + (2613/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7847/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7847/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (166512988806137716356024089471/11015547136000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3451031/500000000000 : ℝ)*(base39) + (397818923311/250000000000 : ℝ)*(base40) + (370629552713/62500000000 : ℝ)*(major_s3_0) + (370629552713/62500000000 : ℝ)*(major_s3_1) + (370629552713/62500000000 : ℝ)*(major_s3_2) + (42917/20000000000 : ℝ)*(sp_s3_0) + (45053843/500000000000 : ℝ)*(sp_s3_2) + (6292037/62500000000 : ℝ)*(sp_s3_7) + (24910441/100000000000 : ℝ)*(sp_s3_15) + (5426883/500000000000 : ℝ)*(sp_s3_16) + (8045210463959/1000000000000 : ℝ)*(sp_s3_21) + (804506417799/100000000000 : ℝ)*(sp_s3_22) + (2011303080237/250000000000 : ℝ)*(sp_s3_23) + (953706841421/250000000000 : ℝ)*(sp_s3_27) + (953706841421/250000000000 : ℝ)*(f.failure) + (10056641603/1250000000 : ℝ)*(f.sum) + (341713209388931269/2933828250000000000000000000000 : ℝ)*base62 + (144360096851521/218625000000000000000000000 : ℝ)*base65 + (1076477662131133/1845175000000000000000000000 : ℝ)*base66 + (204482031907/2484375000000000000000000 : ℝ)*base68 + (182988865902778003/447744000000000000000000000000 : ℝ)*base71 + (262625005786019/307200000000000000000000000 : ℝ)*base72 + (117868329252209/1845175000000000000000000000 : ℝ)*base74 + (50184192233233/153600000000000000000000000 : ℝ)*base77 + (20599060363490185037/22673510400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1451/3125000000000000 : ℝ)*base87 + (1451/3125000000000000 : ℝ)*base89 + (1451/3125000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((1536/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1536/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-73807/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-73807/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1749/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1749/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8133/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8133/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7813/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7813/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7847/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7847/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307086_s3 p hpa hpb X hX hprev2

#print axioms solution
