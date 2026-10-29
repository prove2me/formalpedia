-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312055_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:19:25.241516+00:00
-- url     : https://prove2.me/submissions/146189e8-297d-4198-9493-aae4ba595589

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
theorem collision_support_c312055_s3_s3_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-560940193/2500000000 : ℝ)*x 0 + (5536811621/10000000000 : ℝ)*x 1 + (946249209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560940193/2500000000 : ℝ)^73 ≤ (14750085241213/100000000000000 : ℝ)^57 := by
    have hnat : (560940193 : ℕ)^73*100000000000000^57 ≤ 14750085241213^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560940193 2500000000 14750085241213 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5536811621/10000000000 : ℝ)^73 ≤ (23451051092397/50000000000000 : ℝ)^57 := by
    have hnat : (5536811621 : ℕ)^73*50000000000000^57 ≤ 23451051092397^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536811621 10000000000 23451051092397 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946249209/2000000000 : ℝ)^73 ≤ (4793476570049/12500000000000 : ℝ)^57 := by
    have hnat : (946249209 : ℕ)^73*12500000000000^57 ≤ 4793476570049^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946249209 2000000000 4793476570049 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-560940193/2500000000 : ℝ), (5536811621/10000000000 : ℝ), (946249209/2000000000 : ℝ)] ![(14750085241213/100000000000000 : ℝ), (23451051092397/50000000000000 : ℝ), (4793476570049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-560940193/2500000000 : ℝ)|^73 ≤ (14750085241213/100000000000000 : ℝ)^57
        have hw : |(-560940193/2500000000 : ℝ)|=(560940193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5536811621/10000000000 : ℝ)|^73 ≤ (23451051092397/50000000000000 : ℝ)^57
        have hw : |(5536811621/10000000000 : ℝ)|=(5536811621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(946249209/2000000000 : ℝ)|^73 ≤ (4793476570049/12500000000000 : ℝ)^57
        have hw : |(946249209/2000000000 : ℝ)|=(946249209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (945703191/2000000000 : ℝ)*x 0 + (5529600401/10000000000 : ℝ)*x 1 + (-2256407189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945703191/2000000000 : ℝ)^73 ≤ (19159737748159/50000000000000 : ℝ)^57 := by
    have hnat : (945703191 : ℕ)^73*50000000000000^57 ≤ 19159737748159^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945703191 2000000000 19159737748159 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529600401/10000000000 : ℝ)^73 ≤ (46823883611249/100000000000000 : ℝ)^57 := by
    have hnat : (5529600401 : ℕ)^73*100000000000000^57 ≤ 46823883611249^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529600401 10000000000 46823883611249 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256407189/10000000000 : ℝ)^73 ≤ (14856640879137/100000000000000 : ℝ)^57 := by
    have hnat : (2256407189 : ℕ)^73*100000000000000^57 ≤ 14856640879137^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256407189 10000000000 14856640879137 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(945703191/2000000000 : ℝ), (5529600401/10000000000 : ℝ), (-2256407189/10000000000 : ℝ)] ![(19159737748159/50000000000000 : ℝ), (46823883611249/100000000000000 : ℝ), (14856640879137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(945703191/2000000000 : ℝ)|^73 ≤ (19159737748159/50000000000000 : ℝ)^57
        have hw : |(945703191/2000000000 : ℝ)|=(945703191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529600401/10000000000 : ℝ)|^73 ≤ (46823883611249/100000000000000 : ℝ)^57
        have hw : |(5529600401/10000000000 : ℝ)|=(5529600401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2256407189/10000000000 : ℝ)|^73 ≤ (14856640879137/100000000000000 : ℝ)^57
        have hw : |(-2256407189/10000000000 : ℝ)|=(2256407189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2949674283/5000000000 : ℝ)*x 0 + (801294023/2000000000 : ℝ)*x 1 + (32959203/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2949674283/5000000000 : ℝ)^73 ≤ (25435387514163/50000000000000 : ℝ)^57 := by
    have hnat : (2949674283 : ℕ)^73*50000000000000^57 ≤ 25435387514163^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949674283 5000000000 25435387514163 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801294023/2000000000 : ℝ)^73 ≤ (7748122650133/25000000000000 : ℝ)^57 := by
    have hnat : (801294023 : ℕ)^73*25000000000000^57 ≤ 7748122650133^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801294023 2000000000 7748122650133 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32959203/125000000 : ℝ)^73 ≤ (9068367177433/50000000000000 : ℝ)^57 := by
    have hnat : (32959203 : ℕ)^73*50000000000000^57 ≤ 9068367177433^57*125000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32959203 125000000 9068367177433 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2949674283/5000000000 : ℝ), (801294023/2000000000 : ℝ), (32959203/125000000 : ℝ)] ![(25435387514163/50000000000000 : ℝ), (7748122650133/25000000000000 : ℝ), (9068367177433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2949674283/5000000000 : ℝ)|^73 ≤ (25435387514163/50000000000000 : ℝ)^57
        have hw : |(2949674283/5000000000 : ℝ)|=(2949674283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(801294023/2000000000 : ℝ)|^73 ≤ (7748122650133/25000000000000 : ℝ)^57
        have hw : |(801294023/2000000000 : ℝ)|=(801294023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32959203/125000000 : ℝ)|^73 ≤ (9068367177433/50000000000000 : ℝ)^57
        have hw : |(32959203/125000000 : ℝ)|=(32959203/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4084371/20000000 : ℝ)*x 0 + (5021507561/10000000000 : ℝ)*x 1 + (2705367103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4084371/20000000 : ℝ)^73 ≤ (13074879567027/100000000000000 : ℝ)^57 := by
    have hnat : (4084371 : ℕ)^73*100000000000000^57 ≤ 13074879567027^57*20000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4084371 20000000 13074879567027 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5021507561/10000000000 : ℝ)^73 ≤ (5173300988217/12500000000000 : ℝ)^57 := by
    have hnat : (5021507561 : ℕ)^73*12500000000000^57 ≤ 5173300988217^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021507561 10000000000 5173300988217 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705367103/5000000000 : ℝ)^73 ≤ (22769356254881/50000000000000 : ℝ)^57 := by
    have hnat : (2705367103 : ℕ)^73*50000000000000^57 ≤ 22769356254881^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705367103 5000000000 22769356254881 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4084371/20000000 : ℝ), (5021507561/10000000000 : ℝ), (2705367103/5000000000 : ℝ)] ![(13074879567027/100000000000000 : ℝ), (5173300988217/12500000000000 : ℝ), (22769356254881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4084371/20000000 : ℝ)|^73 ≤ (13074879567027/100000000000000 : ℝ)^57
        have hw : |(-4084371/20000000 : ℝ)|=(4084371/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5021507561/10000000000 : ℝ)|^73 ≤ (5173300988217/12500000000000 : ℝ)^57
        have hw : |(5021507561/10000000000 : ℝ)|=(5021507561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705367103/5000000000 : ℝ)|^73 ≤ (22769356254881/50000000000000 : ℝ)^57
        have hw : |(2705367103/5000000000 : ℝ)|=(2705367103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4647019301/10000000000 : ℝ)*x 0 + (-457039291/5000000000 : ℝ)*x 1 + (3261336753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4647019301/10000000000 : ℝ)^73 ≤ (37475701224849/100000000000000 : ℝ)^57 := by
    have hnat : (4647019301 : ℕ)^73*100000000000000^57 ≤ 37475701224849^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647019301 10000000000 37475701224849 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457039291/5000000000 : ℝ)^73 ≤ (1167534698831/25000000000000 : ℝ)^57 := by
    have hnat : (457039291 : ℕ)^73*25000000000000^57 ≤ 1167534698831^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457039291 5000000000 1167534698831 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3261336753/5000000000 : ℝ)^73 ≤ (57854159959877/100000000000000 : ℝ)^57 := by
    have hnat : (3261336753 : ℕ)^73*100000000000000^57 ≤ 57854159959877^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3261336753 5000000000 57854159959877 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4647019301/10000000000 : ℝ), (-457039291/5000000000 : ℝ), (3261336753/5000000000 : ℝ)] ![(37475701224849/100000000000000 : ℝ), (1167534698831/25000000000000 : ℝ), (57854159959877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4647019301/10000000000 : ℝ)|^73 ≤ (37475701224849/100000000000000 : ℝ)^57
        have hw : |(4647019301/10000000000 : ℝ)|=(4647019301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-457039291/5000000000 : ℝ)|^73 ≤ (1167534698831/25000000000000 : ℝ)^57
        have hw : |(-457039291/5000000000 : ℝ)|=(457039291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3261336753/5000000000 : ℝ)|^73 ≤ (57854159959877/100000000000000 : ℝ)^57
        have hw : |(3261336753/5000000000 : ℝ)|=(3261336753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4640536463/10000000000 : ℝ)*x 0 + (121807519/200000000 : ℝ)*x 1 + (-1604654329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4640536463/10000000000 : ℝ)^73 ≤ (4676094812329/12500000000000 : ℝ)^57 := by
    have hnat : (4640536463 : ℕ)^73*12500000000000^57 ≤ 4676094812329^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4640536463 10000000000 4676094812329 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121807519/200000000 : ℝ)^73 ≤ (10597985452861/20000000000000 : ℝ)^57 := by
    have hnat : (121807519 : ℕ)^73*20000000000000^57 ≤ 10597985452861^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121807519 200000000 10597985452861 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1604654329/10000000000 : ℝ)^73 ≤ (1920262843393/20000000000000 : ℝ)^57 := by
    have hnat : (1604654329 : ℕ)^73*20000000000000^57 ≤ 1920262843393^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604654329 10000000000 1920262843393 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4640536463/10000000000 : ℝ), (121807519/200000000 : ℝ), (-1604654329/10000000000 : ℝ)] ![(4676094812329/12500000000000 : ℝ), (10597985452861/20000000000000 : ℝ), (1920262843393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4640536463/10000000000 : ℝ)|^73 ≤ (4676094812329/12500000000000 : ℝ)^57
        have hw : |(4640536463/10000000000 : ℝ)|=(4640536463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121807519/200000000 : ℝ)|^73 ≤ (10597985452861/20000000000000 : ℝ)^57
        have hw : |(121807519/200000000 : ℝ)|=(121807519/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1604654329/10000000000 : ℝ)|^73 ≤ (1920262843393/20000000000000 : ℝ)^57
        have hw : |(-1604654329/10000000000 : ℝ)|=(1604654329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5407191067/10000000000 : ℝ)*x 0 + (5262775083/10000000000 : ℝ)*x 1 + (863546669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407191067/10000000000 : ℝ)^73 ≤ (22750262522817/50000000000000 : ℝ)^57 := by
    have hnat : (5407191067 : ℕ)^73*50000000000000^57 ≤ 22750262522817^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407191067 10000000000 22750262522817 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262775083/10000000000 : ℝ)^73 ≤ (21975022184493/50000000000000 : ℝ)^57 := by
    have hnat : (5262775083 : ℕ)^73*50000000000000^57 ≤ 21975022184493^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262775083 10000000000 21975022184493 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863546669/5000000000 : ℝ)^73 ≤ (10549430576561/100000000000000 : ℝ)^57 := by
    have hnat : (863546669 : ℕ)^73*100000000000000^57 ≤ 10549430576561^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863546669 5000000000 10549430576561 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407191067/10000000000 : ℝ), (5262775083/10000000000 : ℝ), (863546669/5000000000 : ℝ)] ![(22750262522817/50000000000000 : ℝ), (21975022184493/50000000000000 : ℝ), (10549430576561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407191067/10000000000 : ℝ)|^73 ≤ (22750262522817/50000000000000 : ℝ)^57
        have hw : |(5407191067/10000000000 : ℝ)|=(5407191067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262775083/10000000000 : ℝ)|^73 ≤ (21975022184493/50000000000000 : ℝ)^57
        have hw : |(5262775083/10000000000 : ℝ)|=(5262775083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(863546669/5000000000 : ℝ)|^73 ≤ (10549430576561/100000000000000 : ℝ)^57
        have hw : |(863546669/5000000000 : ℝ)|=(863546669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-759217081/5000000000 : ℝ)*x 0 + (5335407703/10000000000 : ℝ)*x 1 + (5483633947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (759217081/5000000000 : ℝ)^73 ≤ (1789131957713/20000000000000 : ℝ)^57 := by
    have hnat : (759217081 : ℕ)^73*20000000000000^57 ≤ 1789131957713^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759217081 5000000000 1789131957713 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5335407703/10000000000 : ℝ)^73 ≤ (44728370981699/100000000000000 : ℝ)^57 := by
    have hnat : (5335407703 : ℕ)^73*100000000000000^57 ≤ 44728370981699^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5335407703 10000000000 44728370981699 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483633947/10000000000 : ℝ)^73 ≤ (46325969213421/100000000000000 : ℝ)^57 := by
    have hnat : (5483633947 : ℕ)^73*100000000000000^57 ≤ 46325969213421^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483633947 10000000000 46325969213421 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-759217081/5000000000 : ℝ), (5335407703/10000000000 : ℝ), (5483633947/10000000000 : ℝ)] ![(1789131957713/20000000000000 : ℝ), (44728370981699/100000000000000 : ℝ), (46325969213421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-759217081/5000000000 : ℝ)|^73 ≤ (1789131957713/20000000000000 : ℝ)^57
        have hw : |(-759217081/5000000000 : ℝ)|=(759217081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5335407703/10000000000 : ℝ)|^73 ≤ (44728370981699/100000000000000 : ℝ)^57
        have hw : |(5335407703/10000000000 : ℝ)|=(5335407703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483633947/10000000000 : ℝ)|^73 ≤ (46325969213421/100000000000000 : ℝ)^57
        have hw : |(5483633947/10000000000 : ℝ)|=(5483633947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (873859589/2000000000 : ℝ)*x 0 + (-267249337/2000000000 : ℝ)*x 1 + (52124467/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873859589/2000000000 : ℝ)^73 ≤ (2164485097859/6250000000000 : ℝ)^57 := by
    have hnat : (873859589 : ℕ)^73*6250000000000^57 ≤ 2164485097859^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873859589 2000000000 2164485097859 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267249337/2000000000 : ℝ)^73 ≤ (1518977997119/20000000000000 : ℝ)^57 := by
    have hnat : (267249337 : ℕ)^73*20000000000000^57 ≤ 1518977997119^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267249337 2000000000 1518977997119 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52124467/80000000 : ℝ)^73 ≤ (57773348427131/100000000000000 : ℝ)^57 := by
    have hnat : (52124467 : ℕ)^73*100000000000000^57 ≤ 57773348427131^57*80000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52124467 80000000 57773348427131 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873859589/2000000000 : ℝ), (-267249337/2000000000 : ℝ), (52124467/80000000 : ℝ)] ![(2164485097859/6250000000000 : ℝ), (1518977997119/20000000000000 : ℝ), (57773348427131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873859589/2000000000 : ℝ)|^73 ≤ (2164485097859/6250000000000 : ℝ)^57
        have hw : |(873859589/2000000000 : ℝ)|=(873859589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267249337/2000000000 : ℝ)|^73 ≤ (1518977997119/20000000000000 : ℝ)^57
        have hw : |(-267249337/2000000000 : ℝ)|=(267249337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52124467/80000000 : ℝ)|^73 ≤ (57773348427131/100000000000000 : ℝ)^57
        have hw : |(52124467/80000000 : ℝ)|=(52124467/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1096303339/2000000000 : ℝ)*x 0 + (5328167517/10000000000 : ℝ)*x 1 + (-382938597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096303339/2000000000 : ℝ)^73 ≤ (9260612602383/20000000000000 : ℝ)^57 := by
    have hnat : (1096303339 : ℕ)^73*20000000000000^57 ≤ 9260612602383^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096303339 2000000000 9260612602383 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5328167517/10000000000 : ℝ)^73 ≤ (44650651401091/100000000000000 : ℝ)^57 := by
    have hnat : (5328167517 : ℕ)^73*100000000000000^57 ≤ 44650651401091^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5328167517 10000000000 44650651401091 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382938597/2500000000 : ℝ)^73 ≤ (1809257114067/20000000000000 : ℝ)^57 := by
    have hnat : (382938597 : ℕ)^73*20000000000000^57 ≤ 1809257114067^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382938597 2500000000 1809257114067 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1096303339/2000000000 : ℝ), (5328167517/10000000000 : ℝ), (-382938597/2500000000 : ℝ)] ![(9260612602383/20000000000000 : ℝ), (44650651401091/100000000000000 : ℝ), (1809257114067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1096303339/2000000000 : ℝ)|^73 ≤ (9260612602383/20000000000000 : ℝ)^57
        have hw : |(1096303339/2000000000 : ℝ)|=(1096303339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5328167517/10000000000 : ℝ)|^73 ≤ (44650651401091/100000000000000 : ℝ)^57
        have hw : |(5328167517/10000000000 : ℝ)|=(5328167517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382938597/2500000000 : ℝ)|^73 ≤ (1809257114067/20000000000000 : ℝ)^57
        have hw : |(-382938597/2500000000 : ℝ)|=(382938597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3399170279/5000000000 : ℝ)*x 0 + (1866843473/5000000000 : ℝ)*x 1 + (1743728947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3399170279/5000000000 : ℝ)^73 ≤ (15250993281481/25000000000000 : ℝ)^57 := by
    have hnat : (3399170279 : ℕ)^73*25000000000000^57 ≤ 15250993281481^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3399170279 5000000000 15250993281481 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866843473/5000000000 : ℝ)^73 ≤ (28316284011937/100000000000000 : ℝ)^57 := by
    have hnat : (1866843473 : ℕ)^73*100000000000000^57 ≤ 28316284011937^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866843473 5000000000 28316284011937 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1743728947/10000000000 : ℝ)^73 ≤ (2135948567929/20000000000000 : ℝ)^57 := by
    have hnat : (1743728947 : ℕ)^73*20000000000000^57 ≤ 2135948567929^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743728947 10000000000 2135948567929 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3399170279/5000000000 : ℝ), (1866843473/5000000000 : ℝ), (1743728947/10000000000 : ℝ)] ![(15250993281481/25000000000000 : ℝ), (28316284011937/100000000000000 : ℝ), (2135948567929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3399170279/5000000000 : ℝ)|^73 ≤ (15250993281481/25000000000000 : ℝ)^57
        have hw : |(3399170279/5000000000 : ℝ)|=(3399170279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1866843473/5000000000 : ℝ)|^73 ≤ (28316284011937/100000000000000 : ℝ)^57
        have hw : |(1866843473/5000000000 : ℝ)|=(1866843473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1743728947/10000000000 : ℝ)|^73 ≤ (2135948567929/20000000000000 : ℝ)^57
        have hw : |(1743728947/10000000000 : ℝ)|=(1743728947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-762084887/5000000000 : ℝ)*x 0 + (1506130213/2500000000 : ℝ)*x 1 + (95406263/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (762084887/5000000000 : ℝ)^73 ≤ (8988958418337/100000000000000 : ℝ)^57 := by
    have hnat : (762084887 : ℕ)^73*100000000000000^57 ≤ 8988958418337^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762084887 5000000000 8988958418337 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506130213/2500000000 : ℝ)^73 ≤ (6532153592599/12500000000000 : ℝ)^57 := by
    have hnat : (1506130213 : ℕ)^73*12500000000000^57 ≤ 6532153592599^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506130213 2500000000 6532153592599 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95406263/200000000 : ℝ)^73 ≤ (4844226603829/12500000000000 : ℝ)^57 := by
    have hnat : (95406263 : ℕ)^73*12500000000000^57 ≤ 4844226603829^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95406263 200000000 4844226603829 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-762084887/5000000000 : ℝ), (1506130213/2500000000 : ℝ), (95406263/200000000 : ℝ)] ![(8988958418337/100000000000000 : ℝ), (6532153592599/12500000000000 : ℝ), (4844226603829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-762084887/5000000000 : ℝ)|^73 ≤ (8988958418337/100000000000000 : ℝ)^57
        have hw : |(-762084887/5000000000 : ℝ)|=(762084887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506130213/2500000000 : ℝ)|^73 ≤ (6532153592599/12500000000000 : ℝ)^57
        have hw : |(1506130213/2500000000 : ℝ)|=(1506130213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95406263/200000000 : ℝ)|^73 ≤ (4844226603829/12500000000000 : ℝ)^57
        have hw : |(95406263/200000000 : ℝ)|=(95406263/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5482265139/10000000000 : ℝ)*x 0 + (-443383609/5000000000 : ℝ)*x 1 + (5747202801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5482265139/10000000000 : ℝ)^73 ≤ (46311160020837/100000000000000 : ℝ)^57 := by
    have hnat : (5482265139 : ℕ)^73*100000000000000^57 ≤ 46311160020837^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482265139 10000000000 46311160020837 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443383609/5000000000 : ℝ)^73 ≤ (2246094121471/50000000000000 : ℝ)^57 := by
    have hnat : (443383609 : ℕ)^73*50000000000000^57 ≤ 2246094121471^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443383609 5000000000 2246094121471 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5747202801/10000000000 : ℝ)^73 ≤ (24598325862213/50000000000000 : ℝ)^57 := by
    have hnat : (5747202801 : ℕ)^73*50000000000000^57 ≤ 24598325862213^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5747202801 10000000000 24598325862213 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5482265139/10000000000 : ℝ), (-443383609/5000000000 : ℝ), (5747202801/10000000000 : ℝ)] ![(46311160020837/100000000000000 : ℝ), (2246094121471/50000000000000 : ℝ), (24598325862213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5482265139/10000000000 : ℝ)|^73 ≤ (46311160020837/100000000000000 : ℝ)^57
        have hw : |(5482265139/10000000000 : ℝ)|=(5482265139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443383609/5000000000 : ℝ)|^73 ≤ (2246094121471/50000000000000 : ℝ)^57
        have hw : |(-443383609/5000000000 : ℝ)|=(443383609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5747202801/10000000000 : ℝ)|^73 ≤ (24598325862213/50000000000000 : ℝ)^57
        have hw : |(5747202801/10000000000 : ℝ)|=(5747202801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (134601323/312500000 : ℝ)*x 0 + (6117688151/10000000000 : ℝ)*x 1 + (-199662173/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134601323/312500000 : ℝ)^73 ≤ (34003092009427/100000000000000 : ℝ)^57 := by
    have hnat : (134601323 : ℕ)^73*100000000000000^57 ≤ 34003092009427^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134601323 312500000 34003092009427 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6117688151/10000000000 : ℝ)^73 ≤ (333090343921/625000000000 : ℝ)^57 := by
    have hnat : (6117688151 : ℕ)^73*625000000000^57 ≤ 333090343921^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6117688151 10000000000 333090343921 625000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199662173/1000000000 : ℝ)^73 ≤ (12702452952827/100000000000000 : ℝ)^57 := by
    have hnat : (199662173 : ℕ)^73*100000000000000^57 ≤ 12702452952827^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199662173 1000000000 12702452952827 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134601323/312500000 : ℝ), (6117688151/10000000000 : ℝ), (-199662173/1000000000 : ℝ)] ![(34003092009427/100000000000000 : ℝ), (333090343921/625000000000 : ℝ), (12702452952827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134601323/312500000 : ℝ)|^73 ≤ (34003092009427/100000000000000 : ℝ)^57
        have hw : |(134601323/312500000 : ℝ)|=(134601323/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6117688151/10000000000 : ℝ)|^73 ≤ (333090343921/625000000000 : ℝ)^57
        have hw : |(6117688151/10000000000 : ℝ)|=(6117688151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199662173/1000000000 : ℝ)|^73 ≤ (12702452952827/100000000000000 : ℝ)^57
        have hw : |(-199662173/1000000000 : ℝ)|=(199662173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312055_s3_s3_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6928280657/10000000000 : ℝ)*x 0 + (1458732879/5000000000 : ℝ)*x 1 + (622459691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6928280657/10000000000 : ℝ)^73 ≤ (62501258554043/100000000000000 : ℝ)^57 := by
    have hnat : (6928280657 : ℕ)^73*100000000000000^57 ≤ 62501258554043^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6928280657 10000000000 62501258554043 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1458732879/5000000000 : ℝ)^73 ≤ (412916220479/2000000000000 : ℝ)^57 := by
    have hnat : (1458732879 : ℕ)^73*2000000000000^57 ≤ 412916220479^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458732879 5000000000 412916220479 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622459691/2500000000 : ℝ)^73 ≤ (3370586081411/20000000000000 : ℝ)^57 := by
    have hnat : (622459691 : ℕ)^73*20000000000000^57 ≤ 3370586081411^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622459691 2500000000 3370586081411 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6928280657/10000000000 : ℝ), (1458732879/5000000000 : ℝ), (622459691/2500000000 : ℝ)] ![(62501258554043/100000000000000 : ℝ), (412916220479/2000000000000 : ℝ), (3370586081411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6928280657/10000000000 : ℝ)|^73 ≤ (62501258554043/100000000000000 : ℝ)^57
        have hw : |(6928280657/10000000000 : ℝ)|=(6928280657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1458732879/5000000000 : ℝ)|^73 ≤ (412916220479/2000000000000 : ℝ)^57
        have hw : |(1458732879/5000000000 : ℝ)|=(1458732879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622459691/2500000000 : ℝ)|^73 ≤ (3370586081411/20000000000000 : ℝ)^57
        have hw : |(622459691/2500000000 : ℝ)|=(622459691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312055_s3 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((24389/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24389/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(617/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(617/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6257/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((737/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(737/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5971/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5971/20000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (24389/50000 : ℝ) ^ (9/2 : ℝ) ≤ (3953738594718811911/100000000000000000000 : ℝ) := by
    have hpowers : (24389/50000 : ℝ)^9 ≤ (3953738594718811911/100000000000000000000 : ℝ)^2 := by
      have hnat : (24389 : ℕ)^9*100000000000000000000^2 ≤ 3953738594718811911^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24389 50000 3953738594718811911 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24389/50000 : ℝ)) (X := (3953738594718811911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0a : (103953738594718811911/100000000000000000000 : ℝ) ≤ (403461629896011/400000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (103953738594718811911/100000000000000000000 : ℝ)^2 ≤ (403461629896011/400000000000000 : ℝ)^9 := by
      have hnat : (103953738594718811911 : ℕ)^2*400000000000000^9 ≤ 403461629896011^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103953738594718811911 100000000000000000000 403461629896011 400000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (403461629896011/400000000000000 : ℝ)) (X := (103953738594718811911/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0b : (53953738594718811911/50000000000000000000 : ℝ) ≤ (10170558132430281/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (53953738594718811911/50000000000000000000 : ℝ)^2 ≤ (10170558132430281/10000000000000000 : ℝ)^9 := by
      have hnat : (53953738594718811911 : ℕ)^2*10000000000000000^9 ≤ 10170558132430281^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53953738594718811911 50000000000000000000 10170558132430281 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10170558132430281/10000000000000000 : ℝ)) (X := (53953738594718811911/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3461629896011/195112000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(42008692515003/2438900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (24389/50000 : ℝ)) (alpha := (3461629896011/195112000000000 : ℝ)) (beta := (42008692515003/2438900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (24389/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3461629896011/195112000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(42008692515003/2438900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (617/1250 : ℝ) ^ (9/2 : ℝ) ≤ (2085250259674627323/50000000000000000000 : ℝ) := by
    have hpowers : (617/1250 : ℝ)^9 ≤ (2085250259674627323/50000000000000000000 : ℝ)^2 := by
      have hnat : (617 : ℕ)^9*50000000000000000000^2 ≤ 2085250259674627323^2*1250^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        617 1250 2085250259674627323 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (617/1250 : ℝ)) (X := (2085250259674627323/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1a : (52085250259674627323/50000000000000000000 : ℝ) ≤ (10091210788909773/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (52085250259674627323/50000000000000000000 : ℝ)^2 ≤ (10091210788909773/10000000000000000 : ℝ)^9 := by
      have hnat : (52085250259674627323 : ℕ)^2*10000000000000000^9 ≤ 10091210788909773^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52085250259674627323 50000000000000000000 10091210788909773 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10091210788909773/10000000000000000 : ℝ)) (X := (52085250259674627323/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1b : (27085250259674627323/25000000000000000000 : ℝ) ≤ (5089812072084309/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (27085250259674627323/25000000000000000000 : ℝ)^2 ≤ (5089812072084309/5000000000000000 : ℝ)^9 := by
      have hnat : (27085250259674627323 : ℕ)^2*5000000000000000^9 ≤ 5089812072084309^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27085250259674627323 25000000000000000000 5089812072084309 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5089812072084309/5000000000000000 : ℝ)) (X := (27085250259674627323/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(91210788909773/4936000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(17682671051769/987200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (617/1250 : ℝ)) (alpha := (91210788909773/4936000000000000 : ℝ)) (beta := (17682671051769/987200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (617/1250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(91210788909773/4936000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(17682671051769/987200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (6257/12500 : ℝ) ^ (9/2 : ℝ) ≤ (4441734943559405263/100000000000000000000 : ℝ) := by
    have hpowers : (6257/12500 : ℝ)^9 ≤ (4441734943559405263/100000000000000000000 : ℝ)^2 := by
      have hnat : (6257 : ℕ)^9*100000000000000000000^2 ≤ 4441734943559405263^2*12500^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257 12500 4441734943559405263 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6257/12500 : ℝ)) (X := (4441734943559405263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2a : (104441734943559405263/100000000000000000000 : ℝ) ≤ (10097043782811483/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (104441734943559405263/100000000000000000000 : ℝ)^2 ≤ (10097043782811483/10000000000000000 : ℝ)^9 := by
      have hnat : (104441734943559405263 : ℕ)^2*10000000000000000^9 ≤ 10097043782811483^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104441734943559405263 100000000000000000000 10097043782811483 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10097043782811483/10000000000000000 : ℝ)) (X := (104441734943559405263/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2b : (54441734943559405263/50000000000000000000 : ℝ) ≤ (10190928796689329/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (54441734943559405263/50000000000000000000 : ℝ)^2 ≤ (10190928796689329/10000000000000000 : ℝ)^9 := by
      have hnat : (54441734943559405263 : ℕ)^2*10000000000000000^9 ≤ 10190928796689329^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54441734943559405263 50000000000000000000 10190928796689329 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10190928796689329/10000000000000000 : ℝ)) (X := (54441734943559405263/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(97043782811483/5005600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(46942506938923/2502800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (6257/12500 : ℝ)) (alpha := (97043782811483/5005600000000000 : ℝ)) (beta := (46942506938923/2502800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6257/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(97043782811483/5005600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(46942506938923/2502800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-560940193/2500000000 : ℝ)*X 0 0+(5536811621/10000000000 : ℝ)*X 0 1+(946249209/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((945703191/2000000000 : ℝ)*X 2 0+(5529600401/10000000000 : ℝ)*X 2 1+(-2256407189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((2949674283/5000000000 : ℝ)*X 0 0+(801294023/2000000000 : ℝ)*X 0 1+(32959203/125000000 : ℝ)*X 0 2+(2949674283/5000000000 : ℝ)*X 1 0+(801294023/2000000000 : ℝ)*X 1 1+(32959203/125000000 : ℝ)*X 1 2+(2949674283/5000000000 : ℝ)*X 2 0+(801294023/2000000000 : ℝ)*X 2 1+(32959203/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-4084371/20000000 : ℝ)*X 0 0+(5021507561/10000000000 : ℝ)*X 0 1+(2705367103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4647019301/10000000000 : ℝ)*X 1 0+(-457039291/5000000000 : ℝ)*X 1 1+(3261336753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4640536463/10000000000 : ℝ)*X 2 0+(121807519/200000000 : ℝ)*X 2 1+(-1604654329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5407191067/10000000000 : ℝ)*X 0 0+(5262775083/10000000000 : ℝ)*X 0 1+(863546669/5000000000 : ℝ)*X 0 2+(5407191067/10000000000 : ℝ)*X 1 0+(5262775083/10000000000 : ℝ)*X 1 1+(863546669/5000000000 : ℝ)*X 1 2+(5407191067/10000000000 : ℝ)*X 2 0+(5262775083/10000000000 : ℝ)*X 2 1+(863546669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-759217081/5000000000 : ℝ)*X 0 0+(5335407703/10000000000 : ℝ)*X 0 1+(5483633947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((873859589/2000000000 : ℝ)*X 1 0+(-267249337/2000000000 : ℝ)*X 1 1+(52124467/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((1096303339/2000000000 : ℝ)*X 2 0+(5328167517/10000000000 : ℝ)*X 2 1+(-382938597/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3399170279/5000000000 : ℝ)*X 0 0+(1866843473/5000000000 : ℝ)*X 0 1+(1743728947/10000000000 : ℝ)*X 0 2+(3399170279/5000000000 : ℝ)*X 1 0+(1866843473/5000000000 : ℝ)*X 1 1+(1743728947/10000000000 : ℝ)*X 1 2+(3399170279/5000000000 : ℝ)*X 2 0+(1866843473/5000000000 : ℝ)*X 2 1+(1743728947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-762084887/5000000000 : ℝ)*X 0 0+(1506130213/2500000000 : ℝ)*X 0 1+(95406263/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((5482265139/10000000000 : ℝ)*X 1 0+(-443383609/5000000000 : ℝ)*X 1 1+(5747202801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((134601323/312500000 : ℝ)*X 2 0+(6117688151/10000000000 : ℝ)*X 2 1+(-199662173/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((6928280657/10000000000 : ℝ)*X 0 0+(1458732879/5000000000 : ℝ)*X 0 1+(622459691/2500000000 : ℝ)*X 0 2+(6928280657/10000000000 : ℝ)*X 1 0+(1458732879/5000000000 : ℝ)*X 1 1+(622459691/2500000000 : ℝ)*X 1 2+(6928280657/10000000000 : ℝ)*X 2 0+(1458732879/5000000000 : ℝ)*X 2 1+(622459691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312055_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((737/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(737/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4442183906329135441796344521/324673852900000000000000000000000 : ℝ) := by norm_num
    linear_combination (50413/100000000000 : ℝ)*(base8) + (400113711569/500000000000 : ℝ)*(base49) + (305171/200000000000 : ℝ)*(base60) + (663350746303/100000000000 : ℝ)*(major_s3_0) + (663350746303/100000000000 : ℝ)*(major_s3_1) + (663350746303/100000000000 : ℝ)*(major_s3_2) + (59019959/1000000000000 : ℝ)*(sp_s3_0) + (26851411/1000000000000 : ℝ)*(sp_s3_6) + (9292720276263/1000000000000 : ℝ)*(sp_s3_7) + (9292659252293/1000000000000 : ℝ)*(sp_s3_8) + (464629815643/50000000000 : ℝ)*(sp_s3_9) + (124193866051/31250000000 : ℝ)*(sp_s3_13) + (120548059/1000000000000 : ℝ)*(sp_s3_15) + (45871873/250000000000 : ℝ)*(sp_s3_23) + (3974230565043/1000000000000 : ℝ)*(f.failure) + (290399368761/31250000000 : ℝ)*(f.sum) + (897599442565996827/3088455200000000000000000000000 : ℝ)*base62 + (13617631137237/50056000000000000000000000 : ℝ)*base65 + (10405876464277/19744000000000000000000000 : ℝ)*base67 + (111431605986059/500560000000000000000000000 : ℝ)*base68 + (802830791944548531/6104078920000000000000000000000 : ℝ)*base71 + (11781292760169/121945000000000000000000000 : ℝ)*base73 + (655251205101/493600000000000000000000000 : ℝ)*base74 + (25497639035211/487780000000000000000000000 : ℝ)*base77 + (880528508187130477/2407682080000000000000000000000 : ℝ)*base79 + (22259/100000000000000000 : ℝ)*base87 + (22259/100000000000000000 : ℝ)*base89 + (22259/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30397/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (188362452257398371205075023/12682572378906250000000000000000 : ℝ) := by norm_num
    linear_combination (2817493/1000000000000 : ℝ)*(base39) + (698226176817/1000000000000 : ℝ)*(base49) + (1703829/1000000000000 : ℝ)*(base60) + (398807873009/62500000000 : ℝ)*(major_s3_0) + (398807873009/62500000000 : ℝ)*(major_s3_1) + (398807873009/62500000000 : ℝ)*(major_s3_2) + (6436183/500000000000 : ℝ)*(sp_s3_2) + (10365629/200000000000 : ℝ)*(sp_s3_7) + (99102589/1000000000000 : ℝ)*(sp_s3_8) + (8938889830631/1000000000000 : ℝ)*(sp_s3_14) + (4469421278093/500000000000 : ℝ)*(sp_s3_15) + (893892878641/100000000000 : ℝ)*(sp_s3_16) + (95570649571/25000000000 : ℝ)*(sp_s3_20) + (39671987/500000000000 : ℝ)*(sp_s3_27) + (3822905326813/1000000000000 : ℝ)*(f.failure) + (1117367707347/125000000000 : ℝ)*(f.sum) + (1479453814396729261/1930284500000000000000000000000 : ℝ)*base62 + (108803816073/9776562500000000000000000 : ℝ)*base64 + (26118740188231/61700000000000000000000000 : ℝ)*base66 + (94540873549149/156425000000000000000000000 : ℝ)*base68 + (21091203964627567/131553425000000000000000000000 : ℝ)*base71 + (1197696297137/5256250000000000000000000 : ℝ)*base72 + (198867093123343/308500000000000000000000000 : ℝ)*base74 + (477038944521/1051250000000000000000000 : ℝ)*base76 + (6585518736708433/10377940000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (61731/100000000000000000 : ℝ)*base86 + (61731/100000000000000000 : ℝ)*base88 + (61731/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5971/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5971/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (92283140617080933118286227329/11769427167625000000000000000000000 : ℝ) := by norm_num
    linear_combination (85928923503/1000000000000 : ℝ)*(base40) + (28291305999/40000000000 : ℝ)*(base49) + (4257887/1000000000000 : ℝ)*(base59) + (95449895041/15625000000 : ℝ)*(major_s3_0) + (95449895041/15625000000 : ℝ)*(major_s3_1) + (95449895041/15625000000 : ℝ)*(major_s3_2) + (26598899/1000000000000 : ℝ)*(sp_s3_0) + (38877721/1000000000000 : ℝ)*(sp_s3_2) + (20491589/1000000000000 : ℝ)*(sp_s3_9) + (87671769/1000000000000 : ℝ)*(sp_s3_20) + (2139422666523/250000000000 : ℝ)*(sp_s3_21) + (8557717264991/1000000000000 : ℝ)*(sp_s3_22) + (8557657895681/1000000000000 : ℝ)*(sp_s3_23) + (3659779014843/1000000000000 : ℝ)*(sp_s3_27) + (914966671653/250000000000 : ℝ)*(f.failure) + (8557717264991/1000000000000 : ℝ)*(f.sum) + (106020156304153103/965142250000000000000000000000 : ℝ)*base62 + (299800311716591/312850000000000000000000000 : ℝ)*base64 + (1214381397101/3856250000000000000000000 : ℝ)*base66 + (88069430816929/156425000000000000000000000 : ℝ)*base68 + (2135046259105079867/3815049325000000000000000000000 : ℝ)*base70 + (272231993139167/609725000000000000000000000 : ℝ)*base72 + (87524453856789/154250000000000000000000000 : ℝ)*base74 + (520970765009/975560000000000000000000 : ℝ)*base76 + (4592927285531659/30096026000000000000000000000 : ℝ)*base79 + (17189/25000000000000000 : ℝ)*base87 + (17189/25000000000000000 : ℝ)*base89 + (17189/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((24389/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24389/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(617/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(617/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6257/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((737/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(737/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5971/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5971/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312055_s3 p hpa hpb X hX hprev2

#print axioms solution
