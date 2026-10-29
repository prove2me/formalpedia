-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308053_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:36:19.596327+00:00
-- url     : https://prove2.me/submissions/f3d33119-7202-4c54-a1f3-f231598ed4b8

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
theorem collision_support_c308053_s3_s3_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018590619/5000000000 : ℝ)*x 0 + (5249894167/10000000000 : ℝ)*x 1 + (1067876293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018590619/5000000000 : ℝ)^69 ≤ (12601865802251/100000000000000 : ℝ)^53 := by
    have hnat : (1018590619 : ℕ)^69*100000000000000^53 ≤ 12601865802251^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018590619 5000000000 12601865802251 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5249894167/10000000000 : ℝ)^69 ≤ (10804575383511/25000000000000 : ℝ)^53 := by
    have hnat : (5249894167 : ℕ)^69*25000000000000^53 ≤ 10804575383511^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249894167 10000000000 10804575383511 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067876293/2000000000 : ℝ)^69 ≤ (22089916322067/50000000000000 : ℝ)^53 := by
    have hnat : (1067876293 : ℕ)^69*50000000000000^53 ≤ 22089916322067^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067876293 2000000000 22089916322067 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018590619/5000000000 : ℝ), (5249894167/10000000000 : ℝ), (1067876293/2000000000 : ℝ)] ![(12601865802251/100000000000000 : ℝ), (10804575383511/25000000000000 : ℝ), (22089916322067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018590619/5000000000 : ℝ)|^69 ≤ (12601865802251/100000000000000 : ℝ)^53
        have hw : |(-1018590619/5000000000 : ℝ)|=(1018590619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5249894167/10000000000 : ℝ)|^69 ≤ (10804575383511/25000000000000 : ℝ)^53
        have hw : |(5249894167/10000000000 : ℝ)|=(5249894167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1067876293/2000000000 : ℝ)|^69 ≤ (22089916322067/50000000000000 : ℝ)^53
        have hw : |(1067876293/2000000000 : ℝ)|=(1067876293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (28514143/62500000 : ℝ)*x 0 + (-1492201609/10000000000 : ℝ)*x 1 + (6370557739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28514143/62500000 : ℝ)^69 ≤ (35999075002167/100000000000000 : ℝ)^53 := by
    have hnat : (28514143 : ℕ)^69*100000000000000^53 ≤ 35999075002167^53*62500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28514143 62500000 35999075002167 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1492201609/10000000000 : ℝ)^69 ≤ (8402662867669/100000000000000 : ℝ)^53 := by
    have hnat : (1492201609 : ℕ)^69*100000000000000^53 ≤ 8402662867669^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492201609 10000000000 8402662867669 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6370557739/10000000000 : ℝ)^69 ≤ (138995655279/250000000000 : ℝ)^53 := by
    have hnat : (6370557739 : ℕ)^69*250000000000^53 ≤ 138995655279^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6370557739 10000000000 138995655279 250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(28514143/62500000 : ℝ), (-1492201609/10000000000 : ℝ), (6370557739/10000000000 : ℝ)] ![(35999075002167/100000000000000 : ℝ), (8402662867669/100000000000000 : ℝ), (138995655279/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(28514143/62500000 : ℝ)|^69 ≤ (35999075002167/100000000000000 : ℝ)^53
        have hw : |(28514143/62500000 : ℝ)|=(28514143/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1492201609/10000000000 : ℝ)|^69 ≤ (8402662867669/100000000000000 : ℝ)^53
        have hw : |(-1492201609/10000000000 : ℝ)|=(1492201609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6370557739/10000000000 : ℝ)|^69 ≤ (138995655279/250000000000 : ℝ)^53
        have hw : |(6370557739/10000000000 : ℝ)|=(6370557739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2291576701/5000000000 : ℝ)*x 0 + (6373915919/10000000000 : ℝ)*x 1 + (-91098819/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2291576701/5000000000 : ℝ)^69 ≤ (18106912531691/50000000000000 : ℝ)^53 := by
    have hnat : (2291576701 : ℕ)^69*50000000000000^53 ≤ 18106912531691^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291576701 5000000000 18106912531691 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6373915919/10000000000 : ℝ)^69 ≤ (5563642098137/10000000000000 : ℝ)^53 := by
    have hnat : (6373915919 : ℕ)^69*10000000000000^53 ≤ 5563642098137^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6373915919 10000000000 5563642098137 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91098819/625000000 : ℝ)^69 ≤ (8149753945859/100000000000000 : ℝ)^53 := by
    have hnat : (91098819 : ℕ)^69*100000000000000^53 ≤ 8149753945859^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91098819 625000000 8149753945859 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2291576701/5000000000 : ℝ), (6373915919/10000000000 : ℝ), (-91098819/625000000 : ℝ)] ![(18106912531691/50000000000000 : ℝ), (5563642098137/10000000000000 : ℝ), (8149753945859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2291576701/5000000000 : ℝ)|^69 ≤ (18106912531691/50000000000000 : ℝ)^53
        have hw : |(2291576701/5000000000 : ℝ)|=(2291576701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6373915919/10000000000 : ℝ)|^69 ≤ (5563642098137/10000000000000 : ℝ)^53
        have hw : |(6373915919/10000000000 : ℝ)|=(6373915919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91098819/625000000 : ℝ)|^69 ≤ (8149753945859/100000000000000 : ℝ)^53
        have hw : |(-91098819/625000000 : ℝ)|=(91098819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1751185227/2500000000 : ℝ)*x 0 + (2796915691/10000000000 : ℝ)*x 1 + (1342410469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1751185227/2500000000 : ℝ)^69 ≤ (31454876931211/50000000000000 : ℝ)^53 := by
    have hnat : (1751185227 : ℕ)^69*50000000000000^53 ≤ 31454876931211^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751185227 2500000000 31454876931211 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796915691/10000000000 : ℝ)^69 ≤ (4759695782073/25000000000000 : ℝ)^53 := by
    have hnat : (2796915691 : ℕ)^69*25000000000000^53 ≤ 4759695782073^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796915691 10000000000 4759695782073 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1342410469/5000000000 : ℝ)^69 ≤ (9025731502497/50000000000000 : ℝ)^53 := by
    have hnat : (1342410469 : ℕ)^69*50000000000000^53 ≤ 9025731502497^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342410469 5000000000 9025731502497 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1751185227/2500000000 : ℝ), (2796915691/10000000000 : ℝ), (1342410469/5000000000 : ℝ)] ![(31454876931211/50000000000000 : ℝ), (4759695782073/25000000000000 : ℝ), (9025731502497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1751185227/2500000000 : ℝ)|^69 ≤ (31454876931211/50000000000000 : ℝ)^53
        have hw : |(1751185227/2500000000 : ℝ)|=(1751185227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796915691/10000000000 : ℝ)|^69 ≤ (4759695782073/25000000000000 : ℝ)^53
        have hw : |(2796915691/10000000000 : ℝ)|=(2796915691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1342410469/5000000000 : ℝ)|^69 ≤ (9025731502497/50000000000000 : ℝ)^53
        have hw : |(1342410469/5000000000 : ℝ)|=(1342410469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1866102353/10000000000 : ℝ)*x 0 + (4173828229/10000000000 : ℝ)*x 1 + (6467034959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1866102353/10000000000 : ℝ)^69 ≤ (11241920381219/100000000000000 : ℝ)^53 := by
    have hnat : (1866102353 : ℕ)^69*100000000000000^53 ≤ 11241920381219^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866102353 10000000000 11241920381219 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4173828229/10000000000 : ℝ)^69 ≤ (32061140780877/100000000000000 : ℝ)^53 := by
    have hnat : (4173828229 : ℕ)^69*100000000000000^53 ≤ 32061140780877^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173828229 10000000000 32061140780877 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6467034959/10000000000 : ℝ)^69 ≤ (56696938836629/100000000000000 : ℝ)^53 := by
    have hnat : (6467034959 : ℕ)^69*100000000000000^53 ≤ 56696938836629^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6467034959 10000000000 56696938836629 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1866102353/10000000000 : ℝ), (4173828229/10000000000 : ℝ), (6467034959/10000000000 : ℝ)] ![(11241920381219/100000000000000 : ℝ), (32061140780877/100000000000000 : ℝ), (56696938836629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1866102353/10000000000 : ℝ)|^69 ≤ (11241920381219/100000000000000 : ℝ)^53
        have hw : |(-1866102353/10000000000 : ℝ)|=(1866102353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4173828229/10000000000 : ℝ)|^69 ≤ (32061140780877/100000000000000 : ℝ)^53
        have hw : |(4173828229/10000000000 : ℝ)|=(4173828229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6467034959/10000000000 : ℝ)|^69 ≤ (56696938836629/100000000000000 : ℝ)^53
        have hw : |(6467034959/10000000000 : ℝ)|=(6467034959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (775351289/2000000000 : ℝ)*x 0 + (-4649003/62500000 : ℝ)*x 1 + (1848159553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (775351289/2000000000 : ℝ)^69 ≤ (14561382250429/50000000000000 : ℝ)^53 := by
    have hnat : (775351289 : ℕ)^69*50000000000000^53 ≤ 14561382250429^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775351289 2000000000 14561382250429 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4649003/62500000 : ℝ)^69 ≤ (3394645816279/100000000000000 : ℝ)^53 := by
    have hnat : (4649003 : ℕ)^69*100000000000000^53 ≤ 3394645816279^53*62500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4649003 62500000 3394645816279 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1848159553/2500000000 : ℝ)^69 ≤ (67482589667463/100000000000000 : ℝ)^53 := by
    have hnat : (1848159553 : ℕ)^69*100000000000000^53 ≤ 67482589667463^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848159553 2500000000 67482589667463 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(775351289/2000000000 : ℝ), (-4649003/62500000 : ℝ), (1848159553/2500000000 : ℝ)] ![(14561382250429/50000000000000 : ℝ), (3394645816279/100000000000000 : ℝ), (67482589667463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(775351289/2000000000 : ℝ)|^69 ≤ (14561382250429/50000000000000 : ℝ)^53
        have hw : |(775351289/2000000000 : ℝ)|=(775351289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4649003/62500000 : ℝ)|^69 ≤ (3394645816279/100000000000000 : ℝ)^53
        have hw : |(-4649003/62500000 : ℝ)|=(4649003/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1848159553/2500000000 : ℝ)|^69 ≤ (67482589667463/100000000000000 : ℝ)^53
        have hw : |(1848159553/2500000000 : ℝ)|=(1848159553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3898057161/10000000000 : ℝ)*x 0 + (7505887591/10000000000 : ℝ)*x 1 + (-232080479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3898057161/10000000000 : ℝ)^69 ≤ (29331257309253/100000000000000 : ℝ)^53 := by
    have hnat : (3898057161 : ℕ)^69*100000000000000^53 ≤ 29331257309253^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3898057161 10000000000 29331257309253 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7505887591/10000000000 : ℝ)^69 ≤ (8603944404147/12500000000000 : ℝ)^53 := by
    have hnat : (7505887591 : ℕ)^69*12500000000000^53 ≤ 8603944404147^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7505887591 10000000000 8603944404147 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232080479/5000000000 : ℝ)^69 ≤ (367437490427/20000000000000 : ℝ)^53 := by
    have hnat : (232080479 : ℕ)^69*20000000000000^53 ≤ 367437490427^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232080479 5000000000 367437490427 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3898057161/10000000000 : ℝ), (7505887591/10000000000 : ℝ), (-232080479/5000000000 : ℝ)] ![(29331257309253/100000000000000 : ℝ), (8603944404147/12500000000000 : ℝ), (367437490427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3898057161/10000000000 : ℝ)|^69 ≤ (29331257309253/100000000000000 : ℝ)^53
        have hw : |(3898057161/10000000000 : ℝ)|=(3898057161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7505887591/10000000000 : ℝ)|^69 ≤ (8603944404147/12500000000000 : ℝ)^53
        have hw : |(7505887591/10000000000 : ℝ)|=(7505887591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232080479/5000000000 : ℝ)|^69 ≤ (367437490427/20000000000000 : ℝ)^53
        have hw : |(-232080479/5000000000 : ℝ)|=(232080479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (819219549/1250000000 : ℝ)*x 0 + (4827601231/10000000000 : ℝ)*x 1 + (771987011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819219549/1250000000 : ℝ)^69 ≤ (28844375603921/50000000000000 : ℝ)^53 := by
    have hnat : (819219549 : ℕ)^69*50000000000000^53 ≤ 28844375603921^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819219549 1250000000 28844375603921 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827601231/10000000000 : ℝ)^69 ≤ (7749685328813/20000000000000 : ℝ)^53 := by
    have hnat : (4827601231 : ℕ)^69*20000000000000^53 ≤ 7749685328813^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827601231 10000000000 7749685328813 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771987011/10000000000 : ℝ)^69 ≤ (1781411068663/50000000000000 : ℝ)^53 := by
    have hnat : (771987011 : ℕ)^69*50000000000000^53 ≤ 1781411068663^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771987011 10000000000 1781411068663 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819219549/1250000000 : ℝ), (4827601231/10000000000 : ℝ), (771987011/10000000000 : ℝ)] ![(28844375603921/50000000000000 : ℝ), (7749685328813/20000000000000 : ℝ), (1781411068663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819219549/1250000000 : ℝ)|^69 ≤ (28844375603921/50000000000000 : ℝ)^53
        have hw : |(819219549/1250000000 : ℝ)|=(819219549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827601231/10000000000 : ℝ)|^69 ≤ (7749685328813/20000000000000 : ℝ)^53
        have hw : |(4827601231/10000000000 : ℝ)|=(4827601231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(771987011/10000000000 : ℝ)|^69 ≤ (1781411068663/50000000000000 : ℝ)^53
        have hw : |(771987011/10000000000 : ℝ)|=(771987011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-980641609/10000000000 : ℝ)*x 0 + (4827235493/10000000000 : ℝ)*x 1 + (6440182489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980641609/10000000000 : ℝ)^69 ≤ (2432375414983/50000000000000 : ℝ)^53 := by
    have hnat : (980641609 : ℕ)^69*50000000000000^53 ≤ 2432375414983^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980641609 10000000000 2432375414983 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827235493/10000000000 : ℝ)^69 ≤ (9686151226267/25000000000000 : ℝ)^53 := by
    have hnat : (4827235493 : ℕ)^69*25000000000000^53 ≤ 9686151226267^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827235493 10000000000 9686151226267 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6440182489/10000000000 : ℝ)^69 ≤ (56390644249827/100000000000000 : ℝ)^53 := by
    have hnat : (6440182489 : ℕ)^69*100000000000000^53 ≤ 56390644249827^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6440182489 10000000000 56390644249827 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-980641609/10000000000 : ℝ), (4827235493/10000000000 : ℝ), (6440182489/10000000000 : ℝ)] ![(2432375414983/50000000000000 : ℝ), (9686151226267/25000000000000 : ℝ), (56390644249827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-980641609/10000000000 : ℝ)|^69 ≤ (2432375414983/50000000000000 : ℝ)^53
        have hw : |(-980641609/10000000000 : ℝ)|=(980641609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827235493/10000000000 : ℝ)|^69 ≤ (9686151226267/25000000000000 : ℝ)^53
        have hw : |(4827235493/10000000000 : ℝ)|=(4827235493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6440182489/10000000000 : ℝ)|^69 ≤ (56390644249827/100000000000000 : ℝ)^53
        have hw : |(6440182489/10000000000 : ℝ)|=(6440182489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3805830113/10000000000 : ℝ)*x 0 + (-908690163/10000000000 : ℝ)*x 1 + (7365787639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3805830113/10000000000 : ℝ)^69 ≤ (28431031242921/100000000000000 : ℝ)^53 := by
    have hnat : (3805830113 : ℕ)^69*100000000000000^53 ≤ 28431031242921^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805830113 10000000000 28431031242921 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908690163/10000000000 : ℝ)^69 ≤ (2202649149719/50000000000000 : ℝ)^53 := by
    have hnat : (908690163 : ℕ)^69*50000000000000^53 ≤ 2202649149719^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908690163 10000000000 2202649149719 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7365787639/10000000000 : ℝ)^69 ≤ (67163670439779/100000000000000 : ℝ)^53 := by
    have hnat : (7365787639 : ℕ)^69*100000000000000^53 ≤ 67163670439779^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7365787639 10000000000 67163670439779 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3805830113/10000000000 : ℝ), (-908690163/10000000000 : ℝ), (7365787639/10000000000 : ℝ)] ![(28431031242921/100000000000000 : ℝ), (2202649149719/50000000000000 : ℝ), (67163670439779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3805830113/10000000000 : ℝ)|^69 ≤ (28431031242921/100000000000000 : ℝ)^53
        have hw : |(3805830113/10000000000 : ℝ)|=(3805830113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908690163/10000000000 : ℝ)|^69 ≤ (2202649149719/50000000000000 : ℝ)^53
        have hw : |(-908690163/10000000000 : ℝ)|=(908690163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7365787639/10000000000 : ℝ)|^69 ≤ (67163670439779/100000000000000 : ℝ)^53
        have hw : |(7365787639/10000000000 : ℝ)|=(7365787639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5770439019/10000000000 : ℝ)*x 0 + (289725249/500000000 : ℝ)*x 1 + (-491012341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5770439019/10000000000 : ℝ)^69 ≤ (24439424088069/50000000000000 : ℝ)^53 := by
    have hnat : (5770439019 : ℕ)^69*50000000000000^53 ≤ 24439424088069^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5770439019 10000000000 24439424088069 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289725249/500000000 : ℝ)^69 ≤ (49144407517479/100000000000000 : ℝ)^53 := by
    have hnat : (289725249 : ℕ)^69*100000000000000^53 ≤ 49144407517479^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289725249 500000000 49144407517479 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491012341/10000000000 : ℝ)^69 ≤ (197674429047/10000000000000 : ℝ)^53 := by
    have hnat : (491012341 : ℕ)^69*10000000000000^53 ≤ 197674429047^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491012341 10000000000 197674429047 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5770439019/10000000000 : ℝ), (289725249/500000000 : ℝ), (-491012341/10000000000 : ℝ)] ![(24439424088069/50000000000000 : ℝ), (49144407517479/100000000000000 : ℝ), (197674429047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5770439019/10000000000 : ℝ)|^69 ≤ (24439424088069/50000000000000 : ℝ)^53
        have hw : |(5770439019/10000000000 : ℝ)|=(5770439019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(289725249/500000000 : ℝ)|^69 ≤ (49144407517479/100000000000000 : ℝ)^53
        have hw : |(289725249/500000000 : ℝ)|=(289725249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491012341/10000000000 : ℝ)|^69 ≤ (197674429047/10000000000000 : ℝ)^53
        have hw : |(-491012341/10000000000 : ℝ)|=(491012341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (176228611/200000000 : ℝ)*x 0 + (1870598079/10000000000 : ℝ)*x 1 + (414646559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176228611/200000000 : ℝ)^69 ≤ (84811874751271/100000000000000 : ℝ)^53 := by
    have hnat : (176228611 : ℕ)^69*100000000000000^53 ≤ 84811874751271^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176228611 200000000 84811874751271 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870598079/10000000000 : ℝ)^69 ≤ (11277192854449/100000000000000 : ℝ)^53 := by
    have hnat : (1870598079 : ℕ)^69*100000000000000^53 ≤ 11277192854449^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870598079 10000000000 11277192854449 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414646559/5000000000 : ℝ)^69 ≤ (977733093229/25000000000000 : ℝ)^53 := by
    have hnat : (414646559 : ℕ)^69*25000000000000^53 ≤ 977733093229^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414646559 5000000000 977733093229 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(176228611/200000000 : ℝ), (1870598079/10000000000 : ℝ), (414646559/5000000000 : ℝ)] ![(84811874751271/100000000000000 : ℝ), (11277192854449/100000000000000 : ℝ), (977733093229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(176228611/200000000 : ℝ)|^69 ≤ (84811874751271/100000000000000 : ℝ)^53
        have hw : |(176228611/200000000 : ℝ)|=(176228611/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1870598079/10000000000 : ℝ)|^69 ≤ (11277192854449/100000000000000 : ℝ)^53
        have hw : |(1870598079/10000000000 : ℝ)|=(1870598079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414646559/5000000000 : ℝ)|^69 ≤ (977733093229/25000000000000 : ℝ)^53
        have hw : |(414646559/5000000000 : ℝ)|=(414646559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-945908611/10000000000 : ℝ)*x 0 + (6214358701/10000000000 : ℝ)*x 1 + (5091473889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945908611/10000000000 : ℝ)^69 ≤ (580205158519/12500000000000 : ℝ)^53 := by
    have hnat : (945908611 : ℕ)^69*12500000000000^53 ≤ 580205158519^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945908611 10000000000 580205158519 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6214358701/10000000000 : ℝ)^69 ≤ (53830125797383/100000000000000 : ℝ)^53 := by
    have hnat : (6214358701 : ℕ)^69*100000000000000^53 ≤ 53830125797383^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6214358701 10000000000 53830125797383 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5091473889/10000000000 : ℝ)^69 ≤ (41528232920441/100000000000000 : ℝ)^53 := by
    have hnat : (5091473889 : ℕ)^69*100000000000000^53 ≤ 41528232920441^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091473889 10000000000 41528232920441 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-945908611/10000000000 : ℝ), (6214358701/10000000000 : ℝ), (5091473889/10000000000 : ℝ)] ![(580205158519/12500000000000 : ℝ), (53830125797383/100000000000000 : ℝ), (41528232920441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-945908611/10000000000 : ℝ)|^69 ≤ (580205158519/12500000000000 : ℝ)^53
        have hw : |(-945908611/10000000000 : ℝ)|=(945908611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6214358701/10000000000 : ℝ)|^69 ≤ (53830125797383/100000000000000 : ℝ)^53
        have hw : |(6214358701/10000000000 : ℝ)|=(6214358701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5091473889/10000000000 : ℝ)|^69 ≤ (41528232920441/100000000000000 : ℝ)^53
        have hw : |(5091473889/10000000000 : ℝ)|=(5091473889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (180745893/312500000 : ℝ)*x 0 + (-55746493/1250000000 : ℝ)*x 1 + (5802163193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180745893/312500000 : ℝ)^69 ≤ (24513498715219/50000000000000 : ℝ)^53 := by
    have hnat : (180745893 : ℕ)^69*50000000000000^53 ≤ 24513498715219^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180745893 312500000 24513498715219 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55746493/1250000000 : ℝ)^69 ≤ (436004861763/25000000000000 : ℝ)^53 := by
    have hnat : (55746493 : ℕ)^69*25000000000000^53 ≤ 436004861763^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55746493 1250000000 436004861763 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5802163193/10000000000 : ℝ)^69 ≤ (12307245776503/25000000000000 : ℝ)^53 := by
    have hnat : (5802163193 : ℕ)^69*25000000000000^53 ≤ 12307245776503^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5802163193 10000000000 12307245776503 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180745893/312500000 : ℝ), (-55746493/1250000000 : ℝ), (5802163193/10000000000 : ℝ)] ![(24513498715219/50000000000000 : ℝ), (436004861763/25000000000000 : ℝ), (12307245776503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180745893/312500000 : ℝ)|^69 ≤ (24513498715219/50000000000000 : ℝ)^53
        have hw : |(180745893/312500000 : ℝ)|=(180745893/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55746493/1250000000 : ℝ)|^69 ≤ (436004861763/25000000000000 : ℝ)^53
        have hw : |(-55746493/1250000000 : ℝ)|=(55746493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5802163193/10000000000 : ℝ)|^69 ≤ (12307245776503/25000000000000 : ℝ)^53
        have hw : |(5802163193/10000000000 : ℝ)|=(5802163193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (188877343/500000000 : ℝ)*x 0 + (295861811/400000000 : ℝ)*x 1 + (-894302133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188877343/500000000 : ℝ)^69 ≤ (28156268712777/100000000000000 : ℝ)^53 := by
    have hnat : (188877343 : ℕ)^69*100000000000000^53 ≤ 28156268712777^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188877343 500000000 28156268712777 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295861811/400000000 : ℝ)^69 ≤ (67529025214159/100000000000000 : ℝ)^53 := by
    have hnat : (295861811 : ℕ)^69*100000000000000^53 ≤ 67529025214159^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295861811 400000000 67529025214159 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894302133/10000000000 : ℝ)^69 ≤ (539338257887/12500000000000 : ℝ)^53 := by
    have hnat : (894302133 : ℕ)^69*12500000000000^53 ≤ 539338257887^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894302133 10000000000 539338257887 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(188877343/500000000 : ℝ), (295861811/400000000 : ℝ), (-894302133/10000000000 : ℝ)] ![(28156268712777/100000000000000 : ℝ), (67529025214159/100000000000000 : ℝ), (539338257887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(188877343/500000000 : ℝ)|^69 ≤ (28156268712777/100000000000000 : ℝ)^53
        have hw : |(188877343/500000000 : ℝ)|=(188877343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(295861811/400000000 : ℝ)|^69 ≤ (67529025214159/100000000000000 : ℝ)^53
        have hw : |(295861811/400000000 : ℝ)|=(295861811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-894302133/10000000000 : ℝ)|^69 ≤ (539338257887/12500000000000 : ℝ)^53
        have hw : |(-894302133/10000000000 : ℝ)|=(894302133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s3_s3_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4458627931/5000000000 : ℝ)*x 0 + (1341731703/10000000000 : ℝ)*x 1 + (153915583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4458627931/5000000000 : ℝ)^69 ≤ (43070181051369/50000000000000 : ℝ)^53 := by
    have hnat : (4458627931 : ℕ)^69*50000000000000^53 ≤ 43070181051369^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4458627931 5000000000 43070181051369 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341731703/10000000000 : ℝ)^69 ≤ (7316771160759/100000000000000 : ℝ)^53 := by
    have hnat : (1341731703 : ℕ)^69*100000000000000^53 ≤ 7316771160759^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341731703 10000000000 7316771160759 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153915583/1250000000 : ℝ)^69 ≤ (817858340823/12500000000000 : ℝ)^53 := by
    have hnat : (153915583 : ℕ)^69*12500000000000^53 ≤ 817858340823^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153915583 1250000000 817858340823 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4458627931/5000000000 : ℝ), (1341731703/10000000000 : ℝ), (153915583/1250000000 : ℝ)] ![(43070181051369/50000000000000 : ℝ), (7316771160759/100000000000000 : ℝ), (817858340823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4458627931/5000000000 : ℝ)|^69 ≤ (43070181051369/50000000000000 : ℝ)^53
        have hw : |(4458627931/5000000000 : ℝ)|=(4458627931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341731703/10000000000 : ℝ)|^69 ≤ (7316771160759/100000000000000 : ℝ)^53
        have hw : |(1341731703/10000000000 : ℝ)|=(1341731703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153915583/1250000000 : ℝ)|^69 ≤ (817858340823/12500000000000 : ℝ)^53
        have hw : |(153915583/1250000000 : ℝ)|=(153915583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308053_s3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((68353/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68353/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37501/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37501/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74083/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74083/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3151/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3151/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58629/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57227/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57227/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (68353/100000 : ℝ) ^ (17/4 : ℝ) ≤ (19848135530470357091/100000000000000000000 : ℝ) := by
    have hpowers : (68353/100000 : ℝ)^17 ≤ (19848135530470357091/100000000000000000000 : ℝ)^4 := by
      have hnat : (68353 : ℕ)^17*100000000000000000000^4 ≤ 19848135530470357091^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68353 100000 19848135530470357091 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68353/100000 : ℝ)) (X := (19848135530470357091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0a : (119848135530470357091/100000000000000000000 : ℝ) ≤ (2608804211035901/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (119848135530470357091/100000000000000000000 : ℝ)^4 ≤ (2608804211035901/2500000000000000 : ℝ)^17 := by
      have hnat : (119848135530470357091 : ℕ)^4*2500000000000000^17 ≤ 2608804211035901^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119848135530470357091 100000000000000000000 2608804211035901 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2608804211035901/2500000000000000 : ℝ)) (X := (119848135530470357091/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0b : (69848135530470357091/50000000000000000000 : ℝ) ≤ (10818352610201369/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (69848135530470357091/50000000000000000000 : ℝ)^4 ≤ (10818352610201369/10000000000000000 : ℝ)^17 := by
      have hnat : (69848135530470357091 : ℕ)^4*10000000000000000^17 ≤ 10818352610201369^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69848135530470357091 50000000000000000000 10818352610201369 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10818352610201369/10000000000000000 : ℝ)) (X := (69848135530470357091/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(108804211035901/1708825000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(76627153211553/1367060000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (68353/100000 : ℝ)) (alpha := (108804211035901/1708825000000000 : ℝ)) (beta := (76627153211553/1367060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68353/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(108804211035901/1708825000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(76627153211553/1367060000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (37501/50000 : ℝ) ^ (17/4 : ℝ) ≤ (7362064151374867353/25000000000000000000 : ℝ) := by
    have hpowers : (37501/50000 : ℝ)^17 ≤ (7362064151374867353/25000000000000000000 : ℝ)^4 := by
      have hnat : (37501 : ℕ)^17*25000000000000000000^4 ≤ 7362064151374867353^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37501 50000 7362064151374867353 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37501/50000 : ℝ)) (X := (7362064151374867353/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1a : (32362064151374867353/25000000000000000000 : ℝ) ≤ (1328267635687859/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (32362064151374867353/25000000000000000000 : ℝ)^4 ≤ (1328267635687859/1250000000000000 : ℝ)^17 := by
      have hnat : (32362064151374867353 : ℕ)^4*1250000000000000^17 ≤ 1328267635687859^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32362064151374867353 25000000000000000000 1328267635687859 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1328267635687859/1250000000000000 : ℝ)) (X := (32362064151374867353/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1b : (19862064151374867353/12500000000000000000 : ℝ) ≤ (11151185171943279/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (19862064151374867353/12500000000000000000 : ℝ)^4 ≤ (11151185171943279/10000000000000000 : ℝ)^17 := by
      have hnat : (19862064151374867353 : ℕ)^4*10000000000000000^17 ≤ 11151185171943279^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19862064151374867353 12500000000000000000 11151185171943279 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11151185171943279/10000000000000000 : ℝ)) (X := (19862064151374867353/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(78267635687859/937525000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(525044086440407/7500200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (37501/50000 : ℝ)) (alpha := (78267635687859/937525000000000 : ℝ)) (beta := (525044086440407/7500200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (37501/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(78267635687859/937525000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(525044086440407/7500200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (74083/100000 : ℝ) ^ (17/4 : ℝ) ≤ (5588997035033158341/20000000000000000000 : ℝ) := by
    have hpowers : (74083/100000 : ℝ)^17 ≤ (5588997035033158341/20000000000000000000 : ℝ)^4 := by
      have hnat : (74083 : ℕ)^17*20000000000000000000^4 ≤ 5588997035033158341^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74083 100000 5588997035033158341 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74083/100000 : ℝ)) (X := (5588997035033158341/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2a : (25588997035033158341/20000000000000000000 : ℝ) ≤ (331155495987399/312500000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (25588997035033158341/20000000000000000000 : ℝ)^4 ≤ (331155495987399/312500000000000 : ℝ)^17 := by
      have hnat : (25588997035033158341 : ℕ)^4*312500000000000^17 ≤ 331155495987399^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25588997035033158341 20000000000000000000 331155495987399 312500000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (331155495987399/312500000000000 : ℝ)) (X := (25588997035033158341/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2b : (15588997035033158341/10000000000000000000 : ℝ) ≤ (2775293962512347/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (15588997035033158341/10000000000000000000 : ℝ)^4 ≤ (2775293962512347/2500000000000000 : ℝ)^17 := by
      have hnat : (15588997035033158341 : ℕ)^4*2500000000000000^17 ≤ 2775293962512347^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15588997035033158341 10000000000000000000 2775293962512347 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2775293962512347/2500000000000000 : ℝ)) (X := (15588997035033158341/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(18655495987399/231509375000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(25209998922631/370415000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (74083/100000 : ℝ)) (alpha := (18655495987399/231509375000000 : ℝ)) (beta := (25209998922631/370415000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (74083/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(18655495987399/231509375000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(25209998922631/370415000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1018590619/5000000000 : ℝ)*X 0 0+(5249894167/10000000000 : ℝ)*X 0 1+(1067876293/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((28514143/62500000 : ℝ)*X 1 0+(-1492201609/10000000000 : ℝ)*X 1 1+(6370557739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2291576701/5000000000 : ℝ)*X 2 0+(6373915919/10000000000 : ℝ)*X 2 1+(-91098819/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((1751185227/2500000000 : ℝ)*X 0 0+(2796915691/10000000000 : ℝ)*X 0 1+(1342410469/5000000000 : ℝ)*X 0 2+(1751185227/2500000000 : ℝ)*X 1 0+(2796915691/10000000000 : ℝ)*X 1 1+(1342410469/5000000000 : ℝ)*X 1 2+(1751185227/2500000000 : ℝ)*X 2 0+(2796915691/10000000000 : ℝ)*X 2 1+(1342410469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1866102353/10000000000 : ℝ)*X 0 0+(4173828229/10000000000 : ℝ)*X 0 1+(6467034959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((775351289/2000000000 : ℝ)*X 1 0+(-4649003/62500000 : ℝ)*X 1 1+(1848159553/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((3898057161/10000000000 : ℝ)*X 2 0+(7505887591/10000000000 : ℝ)*X 2 1+(-232080479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((819219549/1250000000 : ℝ)*X 0 0+(4827601231/10000000000 : ℝ)*X 0 1+(771987011/10000000000 : ℝ)*X 0 2+(819219549/1250000000 : ℝ)*X 1 0+(4827601231/10000000000 : ℝ)*X 1 1+(771987011/10000000000 : ℝ)*X 1 2+(819219549/1250000000 : ℝ)*X 2 0+(4827601231/10000000000 : ℝ)*X 2 1+(771987011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-980641609/10000000000 : ℝ)*X 0 0+(4827235493/10000000000 : ℝ)*X 0 1+(6440182489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((3805830113/10000000000 : ℝ)*X 1 0+(-908690163/10000000000 : ℝ)*X 1 1+(7365787639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5770439019/10000000000 : ℝ)*X 2 0+(289725249/500000000 : ℝ)*X 2 1+(-491012341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((176228611/200000000 : ℝ)*X 0 0+(1870598079/10000000000 : ℝ)*X 0 1+(414646559/5000000000 : ℝ)*X 0 2+(176228611/200000000 : ℝ)*X 1 0+(1870598079/10000000000 : ℝ)*X 1 1+(414646559/5000000000 : ℝ)*X 1 2+(176228611/200000000 : ℝ)*X 2 0+(1870598079/10000000000 : ℝ)*X 2 1+(414646559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-945908611/10000000000 : ℝ)*X 0 0+(6214358701/10000000000 : ℝ)*X 0 1+(5091473889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((180745893/312500000 : ℝ)*X 1 0+(-55746493/1250000000 : ℝ)*X 1 1+(5802163193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((188877343/500000000 : ℝ)*X 2 0+(295861811/400000000 : ℝ)*X 2 1+(-894302133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((4458627931/5000000000 : ℝ)*X 0 0+(1341731703/10000000000 : ℝ)*X 0 1+(153915583/1250000000 : ℝ)*X 0 2+(4458627931/5000000000 : ℝ)*X 1 0+(1341731703/10000000000 : ℝ)*X 1 1+(153915583/1250000000 : ℝ)*X 1 2+(4458627931/5000000000 : ℝ)*X 2 0+(1341731703/10000000000 : ℝ)*X 2 1+(153915583/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((3151/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3151/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (51069249498552646260291123645357/4747434687694975000000000000000000000 : ℝ) := by norm_num
    linear_combination (76137/50000000000 : ℝ)*(base5) + (1826143/1000000000000 : ℝ)*(base49) + (13001323451/62500000000 : ℝ)*(base59) + (468871837379/125000000000 : ℝ)*(major_s3_0) + (468871837379/125000000000 : ℝ)*(major_s3_1) + (468871837379/125000000000 : ℝ)*(major_s3_2) + (34013411/1000000000000 : ℝ)*(sp_s3_0) + (20458669/1000000000000 : ℝ)*(sp_s3_6) + (1021669991277/200000000000 : ℝ)*(sp_s3_7) + (5108069448079/1000000000000 : ℝ)*(sp_s3_8) + (1277062190913/250000000000 : ℝ)*(sp_s3_9) + (2393539861111/1000000000000 : ℝ)*(sp_s3_13) + (314521717/1000000000000 : ℝ)*(sp_s3_15) + (34182221/250000000000 : ℝ)*(sp_s3_23) + (59839046063/25000000000 : ℝ)*(f.failure) + (1277095992449/250000000000 : ℝ)*(f.sum) + (26108718738185678781/138909329150000000000000000000000 : ℝ)*base63 + (31002921538169/74083000000000000000000000 : ℝ)*base65 + (416450637010629/1875050000000000000000000000 : ℝ)*base67 + (175861659479047/926037500000000000000000000 : ℝ)*base69 + (98243519816849955497/253189764950000000000000000000000 : ℝ)*base71 + (17595555033757/341765000000000000000000000 : ℝ)*base72 + (46201583038637/234381250000000000000000000 : ℝ)*base75 + (30504675067149/213603125000000000000000000 : ℝ)*base77 + (34411834182110695047/128165292650000000000000000000000 : ℝ)*base79 + (1207/2500000000000000 : ℝ)*base86 + (1207/2500000000000000 : ℝ)*base88 + (1207/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58629/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25219789647899245084826411994621/1898973875077990000000000000000000000 : ℝ) := by norm_num
    linear_combination (437323/100000000000 : ℝ)*(base27) + (143199/250000000000 : ℝ)*(base39) + (5957861/1000000000000 : ℝ)*(base59) + (944629264431/250000000000 : ℝ)*(major_s3_0) + (944629264431/250000000000 : ℝ)*(major_s3_1) + (944629264431/250000000000 : ℝ)*(major_s3_2) + (9398721/1000000000000 : ℝ)*(sp_s3_0) + (36508337/1000000000000 : ℝ)*(sp_s3_2) + (8804309/125000000000 : ℝ)*(sp_s3_7) + (2572906378643/500000000000 : ℝ)*(sp_s3_14) + (5145892590479/1000000000000 : ℝ)*(sp_s3_15) + (2572928041071/500000000000 : ℝ)*(sp_s3_16) + (2411027278539/1000000000000 : ℝ)*(sp_s3_20) + (2636157/25000000000 : ℝ)*(sp_s3_27) + (2411137098049/1000000000000 : ℝ)*(f.failure) + (5145892590479/1000000000000 : ℝ)*(f.sum) + (13849492464410022471/69454664575000000000000000000000 : ℝ)*base63 + (7368686641109/14816600000000000000000000 : ℝ)*base65 + (54003892218819/937525000000000000000000000 : ℝ)*base67 + (800441725344161/3704150000000000000000000000 : ℝ)*base69 + (7065590347469656949/15824360309375000000000000000000 : ℝ)*base71 + (263880269823173/683530000000000000000000000 : ℝ)*base72 + (154271022232961/937525000000000000000000000 : ℝ)*base75 + (119672300253097/854412500000000000000000000 : ℝ)*base77 + (52468761253630015551/128165292650000000000000000000000 : ℝ)*base78 + (43161/100000000000000000 : ℝ)*base86 + (43161/100000000000000000 : ℝ)*base88 + (43161/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57227/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57227/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32217017688373339299482594599839/4747434687694975000000000000000000000 : ℝ) := by norm_num
    linear_combination (2459787/500000000000 : ℝ)*(base15) + (828095997/7812500000 : ℝ)*(base40) + (452673087267/125000000000 : ℝ)*(major_s3_0) + (452673087267/125000000000 : ℝ)*(major_s3_1) + (452673087267/125000000000 : ℝ)*(major_s3_2) + (29604393/1000000000000 : ℝ)*(sp_s3_0) + (7483561/250000000000 : ℝ)*(sp_s3_1) + (29724043/1000000000000 : ℝ)*(sp_s3_9) + (5217121/500000000000 : ℝ)*(sp_s3_16) + (95739047/1000000000000 : ℝ)*(sp_s3_20) + (4931869308603/1000000000000 : ℝ)*(sp_s3_21) + (2465932029589/500000000000 : ℝ)*(sp_s3_22) + (4931858754711/1000000000000 : ℝ)*(sp_s3_23) + (28884656027/12500000000 : ℝ)*(sp_s3_27) + (2310868221207/1000000000000 : ℝ)*(f.failure) + (1232974728249/250000000000 : ℝ)*(f.sum) + (5252605991079630263/138909329150000000000000000000000 : ℝ)*base63 + (215586297339627/740830000000000000000000000 : ℝ)*base65 + (76301318350209/234381250000000000000000000 : ℝ)*base67 + (909604297064877/1852075000000000000000000000 : ℝ)*base69 + (78326320364310993179/253189764950000000000000000000000 : ℝ)*base70 + (75655211836909/170882500000000000000000000 : ℝ)*base73 + (488876652570393/1875050000000000000000000000 : ℝ)*base75 + (105314123982457/3417650000000000000000000000 : ℝ)*base77 + (39646872231471787351/128165292650000000000000000000000 : ℝ)*base79 + (29823/100000000000000000 : ℝ)*base86 + (29823/100000000000000000 : ℝ)*base88 + (29823/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((68353/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68353/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37501/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37501/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74083/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74083/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3151/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3151/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58629/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57227/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57227/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308053_s3 p hpa hpb X hX hprev2

#print axioms solution
