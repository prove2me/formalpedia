-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:56.094725+00:00
-- url     : https://prove2.me/submissions/c176d434-514b-4855-ae91-5525c3dfd63a

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
theorem collision_support_c314055_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1414510397/10000000000 : ℝ)*x 0 + (5842022293/10000000000 : ℝ)*x 1 + (4976183993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1414510397/10000000000 : ℝ)^75 ≤ (8322657975761/100000000000000 : ℝ)^59 := by
    have hnat : (1414510397 : ℕ)^75*100000000000000^59 ≤ 8322657975761^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414510397 10000000000 8322657975761 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5842022293/10000000000 : ℝ)^75 ≤ (315600974117/625000000000 : ℝ)^59 := by
    have hnat : (5842022293 : ℕ)^75*625000000000^59 ≤ 315600974117^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5842022293 10000000000 315600974117 625000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4976183993/10000000000 : ℝ)^75 ≤ (41181186152717/100000000000000 : ℝ)^59 := by
    have hnat : (4976183993 : ℕ)^75*100000000000000^59 ≤ 41181186152717^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4976183993 10000000000 41181186152717 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1414510397/10000000000 : ℝ), (5842022293/10000000000 : ℝ), (4976183993/10000000000 : ℝ)] ![(8322657975761/100000000000000 : ℝ), (315600974117/625000000000 : ℝ), (41181186152717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1414510397/10000000000 : ℝ)|^75 ≤ (8322657975761/100000000000000 : ℝ)^59
        have hw : |(-1414510397/10000000000 : ℝ)|=(1414510397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5842022293/10000000000 : ℝ)|^75 ≤ (315600974117/625000000000 : ℝ)^59
        have hw : |(5842022293/10000000000 : ℝ)|=(5842022293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4976183993/10000000000 : ℝ)|^75 ≤ (41181186152717/100000000000000 : ℝ)^59
        have hw : |(4976183993/10000000000 : ℝ)|=(4976183993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1215064543/2500000000 : ℝ)*x 0 + (-378195483/10000000000 : ℝ)*x 1 + (131139477/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1215064543/2500000000 : ℝ)^75 ≤ (9991383050223/25000000000000 : ℝ)^59 := by
    have hnat : (1215064543 : ℕ)^75*25000000000000^59 ≤ 9991383050223^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215064543 2500000000 9991383050223 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378195483/10000000000 : ℝ)^75 ≤ (389002419131/25000000000000 : ℝ)^59 := by
    have hnat : (378195483 : ℕ)^75*25000000000000^59 ≤ 389002419131^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378195483 10000000000 389002419131 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131139477/200000000 : ℝ)^75 ≤ (58478458106303/100000000000000 : ℝ)^59 := by
    have hnat : (131139477 : ℕ)^75*100000000000000^59 ≤ 58478458106303^59*200000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131139477 200000000 58478458106303 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1215064543/2500000000 : ℝ), (-378195483/10000000000 : ℝ), (131139477/200000000 : ℝ)] ![(9991383050223/25000000000000 : ℝ), (389002419131/25000000000000 : ℝ), (58478458106303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1215064543/2500000000 : ℝ)|^75 ≤ (9991383050223/25000000000000 : ℝ)^59
        have hw : |(1215064543/2500000000 : ℝ)|=(1215064543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378195483/10000000000 : ℝ)|^75 ≤ (389002419131/25000000000000 : ℝ)^59
        have hw : |(-378195483/10000000000 : ℝ)|=(378195483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131139477/200000000 : ℝ)|^75 ≤ (58478458106303/100000000000000 : ℝ)^59
        have hw : |(131139477/200000000 : ℝ)|=(131139477/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (968509623/2000000000 : ℝ)*x 0 + (1199095087/2000000000 : ℝ)*x 1 + (-1375406117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (968509623/2000000000 : ℝ)^75 ≤ (39780502838631/100000000000000 : ℝ)^59 := by
    have hnat : (968509623 : ℕ)^75*100000000000000^59 ≤ 39780502838631^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968509623 2000000000 39780502838631 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199095087/2000000000 : ℝ)^75 ≤ (13047052712671/25000000000000 : ℝ)^59 := by
    have hnat : (1199095087 : ℕ)^75*25000000000000^59 ≤ 13047052712671^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199095087 2000000000 13047052712671 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375406117/10000000000 : ℝ)^75 ≤ (4015643148941/50000000000000 : ℝ)^59 := by
    have hnat : (1375406117 : ℕ)^75*50000000000000^59 ≤ 4015643148941^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375406117 10000000000 4015643148941 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(968509623/2000000000 : ℝ), (1199095087/2000000000 : ℝ), (-1375406117/10000000000 : ℝ)] ![(39780502838631/100000000000000 : ℝ), (13047052712671/25000000000000 : ℝ), (4015643148941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(968509623/2000000000 : ℝ)|^75 ≤ (39780502838631/100000000000000 : ℝ)^59
        have hw : |(968509623/2000000000 : ℝ)|=(968509623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199095087/2000000000 : ℝ)|^75 ≤ (13047052712671/25000000000000 : ℝ)^59
        have hw : |(1199095087/2000000000 : ℝ)|=(1199095087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1375406117/10000000000 : ℝ)|^75 ≤ (4015643148941/50000000000000 : ℝ)^59
        have hw : |(-1375406117/10000000000 : ℝ)|=(1375406117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-354117473/2000000000 : ℝ)*x 0 + (453983037/1250000000 : ℝ)*x 1 + (6807427699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354117473/2000000000 : ℝ)^75 ≤ (553588409031/5000000000000 : ℝ)^59 := by
    have hnat : (354117473 : ℕ)^75*5000000000000^59 ≤ 553588409031^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354117473 2000000000 553588409031 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453983037/1250000000 : ℝ)^75 ≤ (27595783441363/100000000000000 : ℝ)^59 := by
    have hnat : (453983037 : ℕ)^75*100000000000000^59 ≤ 27595783441363^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453983037 1250000000 27595783441363 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6807427699/10000000000 : ℝ)^75 ≤ (30666224178703/50000000000000 : ℝ)^59 := by
    have hnat : (6807427699 : ℕ)^75*50000000000000^59 ≤ 30666224178703^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6807427699 10000000000 30666224178703 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-354117473/2000000000 : ℝ), (453983037/1250000000 : ℝ), (6807427699/10000000000 : ℝ)] ![(553588409031/5000000000000 : ℝ), (27595783441363/100000000000000 : ℝ), (30666224178703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-354117473/2000000000 : ℝ)|^75 ≤ (553588409031/5000000000000 : ℝ)^59
        have hw : |(-354117473/2000000000 : ℝ)|=(354117473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453983037/1250000000 : ℝ)|^75 ≤ (27595783441363/100000000000000 : ℝ)^59
        have hw : |(453983037/1250000000 : ℝ)|=(453983037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6807427699/10000000000 : ℝ)|^75 ≤ (30666224178703/50000000000000 : ℝ)^59
        have hw : |(6807427699/10000000000 : ℝ)|=(6807427699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1675481163/5000000000 : ℝ)*x 0 + (-10411/500000000 : ℝ)*x 1 + (1596418331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1675481163/5000000000 : ℝ)^75 ≤ (6227904909107/25000000000000 : ℝ)^59 := by
    have hnat : (1675481163 : ℕ)^75*25000000000000^59 ≤ 6227904909107^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675481163 5000000000 6227904909107 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10411/500000000 : ℝ)^75 ≤ (27983963/25000000000000 : ℝ)^59 := by
    have hnat : (10411 : ℕ)^75*25000000000000^59 ≤ 27983963^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10411 500000000 27983963 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596418331/2000000000 : ℝ)^75 ≤ (15017653684211/20000000000000 : ℝ)^59 := by
    have hnat : (1596418331 : ℕ)^75*20000000000000^59 ≤ 15017653684211^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596418331 2000000000 15017653684211 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1675481163/5000000000 : ℝ), (-10411/500000000 : ℝ), (1596418331/2000000000 : ℝ)] ![(6227904909107/25000000000000 : ℝ), (27983963/25000000000000 : ℝ), (15017653684211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1675481163/5000000000 : ℝ)|^75 ≤ (6227904909107/25000000000000 : ℝ)^59
        have hw : |(1675481163/5000000000 : ℝ)|=(1675481163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10411/500000000 : ℝ)|^75 ≤ (27983963/25000000000000 : ℝ)^59
        have hw : |(-10411/500000000 : ℝ)|=(10411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596418331/2000000000 : ℝ)|^75 ≤ (15017653684211/20000000000000 : ℝ)^59
        have hw : |(1596418331/2000000000 : ℝ)|=(1596418331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3329704759/10000000000 : ℝ)*x 0 + (1530129913/2000000000 : ℝ)*x 1 + (-816925447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3329704759/10000000000 : ℝ)^75 ≤ (4942180826169/20000000000000 : ℝ)^59 := by
    have hnat : (3329704759 : ℕ)^75*20000000000000^59 ≤ 4942180826169^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3329704759 10000000000 4942180826169 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1530129913/2000000000 : ℝ)^75 ≤ (8893421608561/12500000000000 : ℝ)^59 := by
    have hnat : (1530129913 : ℕ)^75*12500000000000^59 ≤ 8893421608561^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530129913 2000000000 8893421608561 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (816925447/10000000000 : ℝ)^75 ≤ (129428843227/3125000000000 : ℝ)^59 := by
    have hnat : (816925447 : ℕ)^75*3125000000000^59 ≤ 129428843227^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816925447 10000000000 129428843227 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3329704759/10000000000 : ℝ), (1530129913/2000000000 : ℝ), (-816925447/10000000000 : ℝ)] ![(4942180826169/20000000000000 : ℝ), (8893421608561/12500000000000 : ℝ), (129428843227/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3329704759/10000000000 : ℝ)|^75 ≤ (4942180826169/20000000000000 : ℝ)^59
        have hw : |(3329704759/10000000000 : ℝ)|=(3329704759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1530129913/2000000000 : ℝ)|^75 ≤ (8893421608561/12500000000000 : ℝ)^59
        have hw : |(1530129913/2000000000 : ℝ)|=(1530129913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-816925447/10000000000 : ℝ)|^75 ≤ (129428843227/3125000000000 : ℝ)^59
        have hw : |(-816925447/10000000000 : ℝ)|=(816925447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (834088599/2000000000 : ℝ)*x 0 + (6771270297/10000000000 : ℝ)*x 1 + (1119565719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834088599/2000000000 : ℝ)^75 ≤ (4112356552147/12500000000000 : ℝ)^59 := by
    have hnat : (834088599 : ℕ)^75*12500000000000^59 ≤ 4112356552147^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834088599 2000000000 4112356552147 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6771270297/10000000000 : ℝ)^75 ≤ (30459319437519/50000000000000 : ℝ)^59 := by
    have hnat : (6771270297 : ℕ)^75*50000000000000^59 ≤ 30459319437519^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6771270297 10000000000 30459319437519 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119565719/10000000000 : ℝ)^75 ≤ (1236501738139/20000000000000 : ℝ)^59 := by
    have hnat : (1119565719 : ℕ)^75*20000000000000^59 ≤ 1236501738139^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119565719 10000000000 1236501738139 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834088599/2000000000 : ℝ), (6771270297/10000000000 : ℝ), (1119565719/10000000000 : ℝ)] ![(4112356552147/12500000000000 : ℝ), (30459319437519/50000000000000 : ℝ), (1236501738139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834088599/2000000000 : ℝ)|^75 ≤ (4112356552147/12500000000000 : ℝ)^59
        have hw : |(834088599/2000000000 : ℝ)|=(834088599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6771270297/10000000000 : ℝ)|^75 ≤ (30459319437519/50000000000000 : ℝ)^59
        have hw : |(6771270297/10000000000 : ℝ)|=(6771270297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119565719/10000000000 : ℝ)|^75 ≤ (1236501738139/20000000000000 : ℝ)^59
        have hw : |(1119565719/10000000000 : ℝ)|=(1119565719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-98512459/2000000000 : ℝ)*x 0 + (4216990653/10000000000 : ℝ)*x 1 + (1769689089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98512459/2000000000 : ℝ)^75 ≤ (2177079864763/100000000000000 : ℝ)^59 := by
    have hnat : (98512459 : ℕ)^75*100000000000000^59 ≤ 2177079864763^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98512459 2000000000 2177079864763 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4216990653/10000000000 : ℝ)^75 ≤ (33366329838379/100000000000000 : ℝ)^59 := by
    have hnat : (4216990653 : ℕ)^75*100000000000000^59 ≤ 33366329838379^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216990653 10000000000 33366329838379 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769689089/2500000000 : ℝ)^75 ≤ (3222829514239/5000000000000 : ℝ)^59 := by
    have hnat : (1769689089 : ℕ)^75*5000000000000^59 ≤ 3222829514239^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769689089 2500000000 3222829514239 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98512459/2000000000 : ℝ), (4216990653/10000000000 : ℝ), (1769689089/2500000000 : ℝ)] ![(2177079864763/100000000000000 : ℝ), (33366329838379/100000000000000 : ℝ), (3222829514239/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98512459/2000000000 : ℝ)|^75 ≤ (2177079864763/100000000000000 : ℝ)^59
        have hw : |(-98512459/2000000000 : ℝ)|=(98512459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4216990653/10000000000 : ℝ)|^75 ≤ (33366329838379/100000000000000 : ℝ)^59
        have hw : |(4216990653/10000000000 : ℝ)|=(4216990653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1769689089/2500000000 : ℝ)|^75 ≤ (3222829514239/5000000000000 : ℝ)^59
        have hw : |(1769689089/2500000000 : ℝ)|=(1769689089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2730574939/10000000000 : ℝ)*x 0 + (-113520357/2000000000 : ℝ)*x 1 + (1030040461/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2730574939/10000000000 : ℝ)^75 ≤ (19203211090999/100000000000000 : ℝ)^59 := by
    have hnat : (2730574939 : ℕ)^75*100000000000000^59 ≤ 19203211090999^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730574939 10000000000 19203211090999 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113520357/2000000000 : ℝ)^75 ≤ (2607097736519/100000000000000 : ℝ)^59 := by
    have hnat : (113520357 : ℕ)^75*100000000000000^59 ≤ 2607097736519^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113520357 2000000000 2607097736519 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030040461/1250000000 : ℝ)^75 ≤ (78189691161049/100000000000000 : ℝ)^59 := by
    have hnat : (1030040461 : ℕ)^75*100000000000000^59 ≤ 78189691161049^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030040461 1250000000 78189691161049 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2730574939/10000000000 : ℝ), (-113520357/2000000000 : ℝ), (1030040461/1250000000 : ℝ)] ![(19203211090999/100000000000000 : ℝ), (2607097736519/100000000000000 : ℝ), (78189691161049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2730574939/10000000000 : ℝ)|^75 ≤ (19203211090999/100000000000000 : ℝ)^59
        have hw : |(2730574939/10000000000 : ℝ)|=(2730574939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113520357/2000000000 : ℝ)|^75 ≤ (2607097736519/100000000000000 : ℝ)^59
        have hw : |(-113520357/2000000000 : ℝ)|=(113520357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030040461/1250000000 : ℝ)|^75 ≤ (78189691161049/100000000000000 : ℝ)^59
        have hw : |(1030040461/1250000000 : ℝ)|=(1030040461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1733638851/2500000000 : ℝ)*x 0 + (4399135879/10000000000 : ℝ)*x 1 + (-460565991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1733638851/2500000000 : ℝ)^75 ≤ (62792102988073/100000000000000 : ℝ)^59 := by
    have hnat : (1733638851 : ℕ)^75*100000000000000^59 ≤ 62792102988073^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733638851 2500000000 62792102988073 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4399135879/10000000000 : ℝ)^75 ≤ (17604490038111/50000000000000 : ℝ)^59 := by
    have hnat : (4399135879 : ℕ)^75*50000000000000^59 ≤ 17604490038111^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399135879 10000000000 17604490038111 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460565991/10000000000 : ℝ)^75 ≤ (249864615269/12500000000000 : ℝ)^59 := by
    have hnat : (460565991 : ℕ)^75*12500000000000^59 ≤ 249864615269^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460565991 10000000000 249864615269 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1733638851/2500000000 : ℝ), (4399135879/10000000000 : ℝ), (-460565991/10000000000 : ℝ)] ![(62792102988073/100000000000000 : ℝ), (17604490038111/50000000000000 : ℝ), (249864615269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1733638851/2500000000 : ℝ)|^75 ≤ (62792102988073/100000000000000 : ℝ)^59
        have hw : |(1733638851/2500000000 : ℝ)|=(1733638851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4399135879/10000000000 : ℝ)|^75 ≤ (17604490038111/50000000000000 : ℝ)^59
        have hw : |(4399135879/10000000000 : ℝ)|=(4399135879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460565991/10000000000 : ℝ)|^75 ≤ (249864615269/12500000000000 : ℝ)^59
        have hw : |(-460565991/10000000000 : ℝ)|=(460565991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8301002481/10000000000 : ℝ)*x 0 + (2573741043/10000000000 : ℝ)*x 1 + (67759417/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8301002481/10000000000 : ℝ)^75 ≤ (15784464012833/20000000000000 : ℝ)^59 := by
    have hnat : (8301002481 : ℕ)^75*20000000000000^59 ≤ 15784464012833^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8301002481 10000000000 15784464012833 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573741043/10000000000 : ℝ)^75 ≤ (17812219052711/100000000000000 : ℝ)^59 := by
    have hnat : (2573741043 : ℕ)^75*100000000000000^59 ≤ 17812219052711^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573741043 10000000000 17812219052711 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67759417/1000000000 : ℝ)^75 ≤ (102045652173/3125000000000 : ℝ)^59 := by
    have hnat : (67759417 : ℕ)^75*3125000000000^59 ≤ 102045652173^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67759417 1000000000 102045652173 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8301002481/10000000000 : ℝ), (2573741043/10000000000 : ℝ), (67759417/1000000000 : ℝ)] ![(15784464012833/20000000000000 : ℝ), (17812219052711/100000000000000 : ℝ), (102045652173/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8301002481/10000000000 : ℝ)|^75 ≤ (15784464012833/20000000000000 : ℝ)^59
        have hw : |(8301002481/10000000000 : ℝ)|=(8301002481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2573741043/10000000000 : ℝ)|^75 ≤ (17812219052711/100000000000000 : ℝ)^59
        have hw : |(2573741043/10000000000 : ℝ)|=(2573741043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67759417/1000000000 : ℝ)|^75 ≤ (102045652173/3125000000000 : ℝ)^59
        have hw : |(67759417/1000000000 : ℝ)|=(67759417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-165549801/2000000000 : ℝ)*x 0 + (7311299151/10000000000 : ℝ)*x 1 + (747667349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165549801/2000000000 : ℝ)^75 ≤ (4211603311891/100000000000000 : ℝ)^59 := by
    have hnat : (165549801 : ℕ)^75*100000000000000^59 ≤ 4211603311891^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165549801 2000000000 4211603311891 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7311299151/10000000000 : ℝ)^75 ≤ (16790039962763/25000000000000 : ℝ)^59 := by
    have hnat : (7311299151 : ℕ)^75*25000000000000^59 ≤ 16790039962763^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7311299151 10000000000 16790039962763 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (747667349/2000000000 : ℝ)^75 ≤ (14314118408831/50000000000000 : ℝ)^59 := by
    have hnat : (747667349 : ℕ)^75*50000000000000^59 ≤ 14314118408831^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747667349 2000000000 14314118408831 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-165549801/2000000000 : ℝ), (7311299151/10000000000 : ℝ), (747667349/2000000000 : ℝ)] ![(4211603311891/100000000000000 : ℝ), (16790039962763/25000000000000 : ℝ), (14314118408831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-165549801/2000000000 : ℝ)|^75 ≤ (4211603311891/100000000000000 : ℝ)^59
        have hw : |(-165549801/2000000000 : ℝ)|=(165549801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7311299151/10000000000 : ℝ)|^75 ≤ (16790039962763/25000000000000 : ℝ)^59
        have hw : |(7311299151/10000000000 : ℝ)|=(7311299151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(747667349/2000000000 : ℝ)|^75 ≤ (14314118408831/50000000000000 : ℝ)^59
        have hw : |(747667349/2000000000 : ℝ)|=(747667349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3474964073/5000000000 : ℝ)*x 0 + (-20894599/10000000000 : ℝ)*x 1 + (4573429797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3474964073/5000000000 : ℝ)^75 ≤ (7871138086639/12500000000000 : ℝ)^59 := by
    have hnat : (3474964073 : ℕ)^75*12500000000000^59 ≤ 7871138086639^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3474964073 5000000000 7871138086639 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20894599/10000000000 : ℝ)^75 ≤ (9799493289/25000000000000 : ℝ)^59 := by
    have hnat : (20894599 : ℕ)^75*25000000000000^59 ≤ 9799493289^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20894599 10000000000 9799493289 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4573429797/10000000000 : ℝ)^75 ≤ (4623962165037/12500000000000 : ℝ)^59 := by
    have hnat : (4573429797 : ℕ)^75*12500000000000^59 ≤ 4623962165037^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573429797 10000000000 4623962165037 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3474964073/5000000000 : ℝ), (-20894599/10000000000 : ℝ), (4573429797/10000000000 : ℝ)] ![(7871138086639/12500000000000 : ℝ), (9799493289/25000000000000 : ℝ), (4623962165037/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3474964073/5000000000 : ℝ)|^75 ≤ (7871138086639/12500000000000 : ℝ)^59
        have hw : |(3474964073/5000000000 : ℝ)|=(3474964073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20894599/10000000000 : ℝ)|^75 ≤ (9799493289/25000000000000 : ℝ)^59
        have hw : |(-20894599/10000000000 : ℝ)|=(20894599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4573429797/10000000000 : ℝ)|^75 ≤ (4623962165037/12500000000000 : ℝ)^59
        have hw : |(4573429797/10000000000 : ℝ)|=(4573429797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2359747179/10000000000 : ℝ)*x 0 + (393968567/500000000 : ℝ)*x 1 + (-829128501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2359747179/10000000000 : ℝ)^75 ≤ (638050550049/4000000000000 : ℝ)^59 := by
    have hnat : (2359747179 : ℕ)^75*4000000000000^59 ≤ 638050550049^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359747179 10000000000 638050550049 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393968567/500000000 : ℝ)^75 ≤ (73862071808519/100000000000000 : ℝ)^59 := by
    have hnat : (393968567 : ℕ)^75*100000000000000^59 ≤ 73862071808519^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393968567 500000000 73862071808519 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829128501/5000000000 : ℝ)^75 ≤ (5093332213831/50000000000000 : ℝ)^59 := by
    have hnat : (829128501 : ℕ)^75*50000000000000^59 ≤ 5093332213831^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829128501 5000000000 5093332213831 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2359747179/10000000000 : ℝ), (393968567/500000000 : ℝ), (-829128501/5000000000 : ℝ)] ![(638050550049/4000000000000 : ℝ), (73862071808519/100000000000000 : ℝ), (5093332213831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2359747179/10000000000 : ℝ)|^75 ≤ (638050550049/4000000000000 : ℝ)^59
        have hw : |(2359747179/10000000000 : ℝ)|=(2359747179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(393968567/500000000 : ℝ)|^75 ≤ (73862071808519/100000000000000 : ℝ)^59
        have hw : |(393968567/500000000 : ℝ)|=(393968567/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-829128501/5000000000 : ℝ)|^75 ≤ (5093332213831/50000000000000 : ℝ)^59
        have hw : |(-829128501/5000000000 : ℝ)|=(829128501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2028748629/2500000000 : ℝ)*x 0 + (2114488409/10000000000 : ℝ)*x 1 + (781234769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028748629/2500000000 : ℝ)^75 ≤ (9585139587019/12500000000000 : ℝ)^59 := by
    have hnat : (2028748629 : ℕ)^75*12500000000000^59 ≤ 9585139587019^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028748629 2500000000 9585139587019 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114488409/10000000000 : ℝ)^75 ≤ (6937134944071/50000000000000 : ℝ)^59 := by
    have hnat : (2114488409 : ℕ)^75*50000000000000^59 ≤ 6937134944071^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114488409 10000000000 6937134944071 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (781234769/5000000000 : ℝ)^75 ≤ (4722306697573/50000000000000 : ℝ)^59 := by
    have hnat : (781234769 : ℕ)^75*50000000000000^59 ≤ 4722306697573^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781234769 5000000000 4722306697573 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2028748629/2500000000 : ℝ), (2114488409/10000000000 : ℝ), (781234769/5000000000 : ℝ)] ![(9585139587019/12500000000000 : ℝ), (6937134944071/50000000000000 : ℝ), (4722306697573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2028748629/2500000000 : ℝ)|^75 ≤ (9585139587019/12500000000000 : ℝ)^59
        have hw : |(2028748629/2500000000 : ℝ)|=(2028748629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114488409/10000000000 : ℝ)|^75 ≤ (6937134944071/50000000000000 : ℝ)^59
        have hw : |(2114488409/10000000000 : ℝ)|=(2114488409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(781234769/5000000000 : ℝ)|^75 ≤ (4722306697573/50000000000000 : ℝ)^59
        have hw : |(781234769/5000000000 : ℝ)|=(781234769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314055_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((82293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39973/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39973/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80719/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80719/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12573/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12573/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61511/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61511/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62479/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(62479/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (82293/100000 : ℝ) ^ (37/8 : ℝ) ≤ (1624102295089583697/4000000000000000000 : ℝ) := by
    have hpowers : (82293/100000 : ℝ)^37 ≤ (1624102295089583697/4000000000000000000 : ℝ)^8 := by
      have hnat : (82293 : ℕ)^37*4000000000000000000^8 ≤ 1624102295089583697^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82293 100000 1624102295089583697 4000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82293/100000 : ℝ)) (X := (1624102295089583697/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (5624102295089583697/4000000000000000000 : ℝ) ≤ (2152923160136621/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (5624102295089583697/4000000000000000000 : ℝ)^8 ≤ (2152923160136621/2000000000000000 : ℝ)^37 := by
      have hnat : (5624102295089583697 : ℕ)^8*2000000000000000^37 ≤ 2152923160136621^37*4000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5624102295089583697 4000000000000000000 2152923160136621 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2152923160136621/2000000000000000 : ℝ)) (X := (5624102295089583697/4000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3624102295089583697/2000000000000000000 : ℝ) ≤ (11371575477440749/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3624102295089583697/2000000000000000000 : ℝ)^8 ≤ (11371575477440749/10000000000000000 : ℝ)^37 := by
      have hnat : (3624102295089583697 : ℕ)^8*10000000000000000^37 ≤ 11371575477440749^37*2000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3624102295089583697 2000000000000000000 11371575477440749 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11371575477440749/10000000000000000 : ℝ)) (X := (3624102295089583697/2000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(50974386712207/548620000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(50579973063137/685775000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (82293/100000 : ℝ)) (alpha := (50974386712207/548620000000000 : ℝ)) (beta := (50579973063137/685775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (82293/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(50974386712207/548620000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(50579973063137/685775000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (39973/50000 : ℝ) ^ (37/8 : ℝ) ≤ (35516889078986602841/100000000000000000000 : ℝ) := by
    have hpowers : (39973/50000 : ℝ)^37 ≤ (35516889078986602841/100000000000000000000 : ℝ)^8 := by
      have hnat : (39973 : ℕ)^37*100000000000000000000^8 ≤ 35516889078986602841^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39973 50000 35516889078986602841 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39973/50000 : ℝ)) (X := (35516889078986602841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (135516889078986602841/100000000000000000000 : ℝ) ≤ (10679209799813513/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (135516889078986602841/100000000000000000000 : ℝ)^8 ≤ (10679209799813513/10000000000000000 : ℝ)^37 := by
      have hnat : (135516889078986602841 : ℕ)^8*10000000000000000^37 ≤ 10679209799813513^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        135516889078986602841 100000000000000000000 10679209799813513 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10679209799813513/10000000000000000 : ℝ)) (X := (135516889078986602841/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (85516889078986602841/50000000000000000000 : ℝ) ≤ (11230422216412433/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (85516889078986602841/50000000000000000000 : ℝ)^8 ≤ (11230422216412433/10000000000000000 : ℝ)^37 := by
      have hnat : (85516889078986602841 : ℕ)^8*10000000000000000^37 ≤ 11230422216412433^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85516889078986602841 50000000000000000000 11230422216412433 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11230422216412433/10000000000000000 : ℝ)) (X := (85516889078986602841/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(679209799813513/7994600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(13780310414973/199865000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (39973/50000 : ℝ)) (alpha := (679209799813513/7994600000000000 : ℝ)) (beta := (13780310414973/199865000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39973/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(679209799813513/7994600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(13780310414973/199865000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (80719/100000 : ℝ) ^ (37/8 : ℝ) ≤ (18566624501710531431/50000000000000000000 : ℝ) := by
    have hpowers : (80719/100000 : ℝ)^37 ≤ (18566624501710531431/50000000000000000000 : ℝ)^8 := by
      have hnat : (80719 : ℕ)^37*50000000000000000000^8 ≤ 18566624501710531431^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80719 100000 18566624501710531431 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80719/100000 : ℝ)) (X := (18566624501710531431/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (68566624501710531431/50000000000000000000 : ℝ) ≤ (10706622487725197/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (68566624501710531431/50000000000000000000 : ℝ)^8 ≤ (10706622487725197/10000000000000000 : ℝ)^37 := by
      have hnat : (68566624501710531431 : ℕ)^8*10000000000000000^37 ≤ 10706622487725197^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68566624501710531431 50000000000000000000 10706622487725197 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10706622487725197/10000000000000000 : ℝ)) (X := (68566624501710531431/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (43566624501710531431/25000000000000000000 : ℝ) ≤ (1409497696977897/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (43566624501710531431/25000000000000000000 : ℝ)^8 ≤ (1409497696977897/1250000000000000 : ℝ)^37 := by
      have hnat : (43566624501710531431 : ℕ)^8*1250000000000000^37 ≤ 1409497696977897^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43566624501710531431 25000000000000000000 1409497696977897 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1409497696977897/1250000000000000 : ℝ)) (X := (43566624501710531431/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(706622487725197/8071900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(569359088097979/8071900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (80719/100000 : ℝ)) (alpha := (706622487725197/8071900000000000 : ℝ)) (beta := (569359088097979/8071900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (80719/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(706622487725197/8071900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(569359088097979/8071900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1414510397/10000000000 : ℝ)*X 0 0+(5842022293/10000000000 : ℝ)*X 0 1+(4976183993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1215064543/2500000000 : ℝ)*X 1 0+(-378195483/10000000000 : ℝ)*X 1 1+(131139477/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((968509623/2000000000 : ℝ)*X 2 0+(1199095087/2000000000 : ℝ)*X 2 1+(-1375406117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-354117473/2000000000 : ℝ)*X 0 0+(453983037/1250000000 : ℝ)*X 0 1+(6807427699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1675481163/5000000000 : ℝ)*X 1 0+(-10411/500000000 : ℝ)*X 1 1+(1596418331/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3329704759/10000000000 : ℝ)*X 2 0+(1530129913/2000000000 : ℝ)*X 2 1+(-816925447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((834088599/2000000000 : ℝ)*X 0 0+(6771270297/10000000000 : ℝ)*X 0 1+(1119565719/10000000000 : ℝ)*X 0 2+(834088599/2000000000 : ℝ)*X 1 0+(6771270297/10000000000 : ℝ)*X 1 1+(1119565719/10000000000 : ℝ)*X 1 2+(834088599/2000000000 : ℝ)*X 2 0+(6771270297/10000000000 : ℝ)*X 2 1+(1119565719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-98512459/2000000000 : ℝ)*X 0 0+(4216990653/10000000000 : ℝ)*X 0 1+(1769689089/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2730574939/10000000000 : ℝ)*X 1 0+(-113520357/2000000000 : ℝ)*X 1 1+(1030040461/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1733638851/2500000000 : ℝ)*X 2 0+(4399135879/10000000000 : ℝ)*X 2 1+(-460565991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8301002481/10000000000 : ℝ)*X 0 0+(2573741043/10000000000 : ℝ)*X 0 1+(67759417/1000000000 : ℝ)*X 0 2+(8301002481/10000000000 : ℝ)*X 1 0+(2573741043/10000000000 : ℝ)*X 1 1+(67759417/1000000000 : ℝ)*X 1 2+(8301002481/10000000000 : ℝ)*X 2 0+(2573741043/10000000000 : ℝ)*X 2 1+(67759417/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-165549801/2000000000 : ℝ)*X 0 0+(7311299151/10000000000 : ℝ)*X 0 1+(747667349/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3474964073/5000000000 : ℝ)*X 1 0+(-20894599/10000000000 : ℝ)*X 1 1+(4573429797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2359747179/10000000000 : ℝ)*X 2 0+(393968567/500000000 : ℝ)*X 2 1+(-829128501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2028748629/2500000000 : ℝ)*X 0 0+(2114488409/10000000000 : ℝ)*X 0 1+(781234769/5000000000 : ℝ)*X 0 2+(2028748629/2500000000 : ℝ)*X 1 0+(2114488409/10000000000 : ℝ)*X 1 1+(781234769/5000000000 : ℝ)*X 1 2+(2028748629/2500000000 : ℝ)*X 2 0+(2114488409/10000000000 : ℝ)*X 2 1+(781234769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((12573/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12573/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (254932097940663032775346683/27677536112500000000000000000000 : ℝ) := by norm_num
    linear_combination (373764639987/500000000000 : ℝ)*(base7) + (2729/1953125000 : ℝ)*(base49) + (436651/500000000000 : ℝ)*(base53) + (546219/1000000000000 : ℝ)*(base60) + (16770696111/7812500000 : ℝ)*(major_s1_0) + (16770696111/7812500000 : ℝ)*(major_s1_1) + (1073324114453/500000000000 : ℝ)*(major_s1_2) + (11402427/1000000000000 : ℝ)*(sp_s1_0) + (52156446573/20000000000 : ℝ)*(sp_s1_7) + (1303927613393/500000000000 : ℝ)*(sp_s1_8) + (2607848485027/1000000000000 : ℝ)*(sp_s1_9) + (1995080612409/1000000000000 : ℝ)*(sp_s1_13) + (21495709/1000000000000 : ℝ)*(sp_s1_14) + (7615061/1000000000000 : ℝ)*(sp_s1_23) + (311887833109/250000000000 : ℝ)*(f.failure) + (325982012511/125000000000 : ℝ)*(f.sum) + (802640544192857763/40332257337500000000000000000000 : ℝ)*base63 + (388295169281077/1008987500000000000000000000 : ℝ)*base64 + (3533643992049/99932500000000000000000000 : ℝ)*base66 + (322990509142351/1008987500000000000000000000 : ℝ)*base68 + (3630704876182125257/27677536112500000000000000000000 : ℝ)*base70 + (206873321298663/1371550000000000000000000000 : ℝ)*base72 + (803174798531279/1998650000000000000000000000 : ℝ)*base74 + (2348406262059/13715500000000000000000000 : ℝ)*base76 + (509015579804555247/6853121018750000000000000000000 : ℝ)*base79 + (32521/25000000000000000 : ℝ)*base87 + (32521/25000000000000000 : ℝ)*base89 + (32521/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61511/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61511/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (65883932466172806261837187086843/4425416604099850000000000000000000000 : ℝ) := by norm_num
    linear_combination (625822611531/1000000000000 : ℝ)*(base7) + (187793/20000000000 : ℝ)*(base27) + (12297/20000000000 : ℝ)*(base59) + (963284870309/500000000000 : ℝ)*(major_s1_0) + (963284870309/500000000000 : ℝ)*(major_s1_1) + (963284870309/500000000000 : ℝ)*(major_s1_2) + (12251429/1000000000000 : ℝ)*(sp_s1_0) + (3375603/250000000000 : ℝ)*(sp_s1_2) + (139702221/1000000000000 : ℝ)*(sp_s1_8) + (2366878373197/1000000000000 : ℝ)*(sp_s1_14) + (473350184481/200000000000 : ℝ)*(sp_s1_15) + (473375424443/200000000000 : ℝ)*(sp_s1_16) + (872712922249/500000000000 : ℝ)*(sp_s1_20) + (1845103/50000000000 : ℝ)*(sp_s1_27) + (559824762339/500000000000 : ℝ)*(f.failure) + (2366890624627/1000000000000 : ℝ)*(f.sum) + (166925558264975418681/322658058700000000000000000000000 : ℝ)*base63 + (979996337295771/4035950000000000000000000000 : ℝ)*base65 + (48020887330447/79946000000000000000000000 : ℝ)*base67 + (1041606871359917/1008987500000000000000000000 : ℝ)*base69 + (38799848831786058779/110710144450000000000000000000000 : ℝ)*base70 + (1075171414250407/1371550000000000000000000000 : ℝ)*base73 + (2395205385534777/3997300000000000000000000000 : ℝ)*base75 + (21288646447717/137155000000000000000000000 : ℝ)*base77 + (990652217786925831/54824968150000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (9391/50000000000000000 : ℝ)*base87 + (9391/50000000000000000 : ℝ)*base89 + (9391/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62479/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(62479/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (104566663855127254686737979/22142028890000000000000000000000 : ℝ) := by norm_num
    linear_combination (15395084009/20000000000 : ℝ)*(base7) + (82715340057/1000000000000 : ℝ)*(base40) + (256003/1000000000000 : ℝ)*(base49) + (13183/500000000000 : ℝ)*(base59) + (1860641125267/1000000000000 : ℝ)*(major_s1_0) + (1860641125267/1000000000000 : ℝ)*(major_s1_1) + (1860641125267/1000000000000 : ℝ)*(major_s1_2) + (881603/250000000000 : ℝ)*(sp_s1_1) + (15912479/500000000000 : ℝ)*(sp_s1_9) + (2836671/500000000000 : ℝ)*(sp_s1_20) + (2189039755811/1000000000000 : ℝ)*(sp_s1_21) + (1094518114699/500000000000 : ℝ)*(sp_s1_22) + (2189007930853/1000000000000 : ℝ)*(sp_s1_23) + (925541416053/500000000000 : ℝ)*(sp_s1_27) + (540667152499/500000000000 : ℝ)*(f.failure) + (2189039755811/1000000000000 : ℝ)*(f.sum) + (82533008647584126983/645316117400000000000000000000000 : ℝ)*base63 + (1822509898700597/8071900000000000000000000000 : ℝ)*base64 + (204763494749781/399730000000000000000000000 : ℝ)*base66 + (3206339349300299/8071900000000000000000000000 : ℝ)*base69 + (47492868413274601371/110710144450000000000000000000000 : ℝ)*base70 + (281518075895797/342887500000000000000000000 : ℝ)*base73 + (1089538585523249/7994600000000000000000000000 : ℝ)*base74 + (448313617289431/548620000000000000000000000 : ℝ)*base76 + (754233099879300199/3426560509375000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (431/50000000000000000 : ℝ)*base87 + (431/50000000000000000 : ℝ)*base89 + (431/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((82293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39973/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39973/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80719/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80719/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12573/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12573/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61511/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61511/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62479/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(62479/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314055_s1 p hpa hpb X hX hprev0

#print axioms solution
