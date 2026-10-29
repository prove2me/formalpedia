-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308049_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:34:58.487118+00:00
-- url     : https://prove2.me/submissions/fded6e44-25da-496d-9dc5-ba2d90377947

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
theorem collision_support_c308049_s0_s0_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3470187827/10000000000 : ℝ)*x 0 + (867546923/2500000000 : ℝ)*x 1 + (1158611551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3470187827/10000000000 : ℝ)^35 ≤ (3170087764949/12500000000000 : ℝ)^27 := by
    have hnat : (3470187827 : ℕ)^35*12500000000000^27 ≤ 3170087764949^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470187827 10000000000 3170087764949 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (867546923/2500000000 : ℝ)^35 ≤ (25360700840663/100000000000000 : ℝ)^27 := by
    have hnat : (867546923 : ℕ)^35*100000000000000^27 ≤ 25360700840663^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867546923 2500000000 25360700840663 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158611551/2000000000 : ℝ)^35 ≤ (49278597023413/100000000000000 : ℝ)^27 := by
    have hnat : (1158611551 : ℕ)^35*100000000000000^27 ≤ 49278597023413^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158611551 2000000000 49278597023413 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3470187827/10000000000 : ℝ), (867546923/2500000000 : ℝ), (1158611551/2000000000 : ℝ)] ![(3170087764949/12500000000000 : ℝ), (25360700840663/100000000000000 : ℝ), (49278597023413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3470187827/10000000000 : ℝ)|^35 ≤ (3170087764949/12500000000000 : ℝ)^27
        have hw : |(-3470187827/10000000000 : ℝ)|=(3470187827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(867546923/2500000000 : ℝ)|^35 ≤ (25360700840663/100000000000000 : ℝ)^27
        have hw : |(867546923/2500000000 : ℝ)|=(867546923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1158611551/2000000000 : ℝ)|^35 ≤ (49278597023413/100000000000000 : ℝ)^27
        have hw : |(1158611551/2000000000 : ℝ)|=(1158611551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1179462083/5000000000 : ℝ)*x 0 + (-1179462037/5000000000 : ℝ)*x 1 + (7531523147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1179462083/5000000000 : ℝ)^35 ≤ (15376286235453/100000000000000 : ℝ)^27 := by
    have hnat : (1179462083 : ℕ)^35*100000000000000^27 ≤ 15376286235453^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179462083 5000000000 15376286235453 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1179462037/5000000000 : ℝ)^35 ≤ (96101784113/625000000000 : ℝ)^27 := by
    have hnat : (1179462037 : ℕ)^35*625000000000^27 ≤ 96101784113^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179462037 5000000000 96101784113 625000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7531523147/10000000000 : ℝ)^35 ≤ (69247428303003/100000000000000 : ℝ)^27 := by
    have hnat : (7531523147 : ℕ)^35*100000000000000^27 ≤ 69247428303003^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7531523147 10000000000 69247428303003 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1179462083/5000000000 : ℝ), (-1179462037/5000000000 : ℝ), (7531523147/10000000000 : ℝ)] ![(15376286235453/100000000000000 : ℝ), (96101784113/625000000000 : ℝ), (69247428303003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1179462083/5000000000 : ℝ)|^35 ≤ (15376286235453/100000000000000 : ℝ)^27
        have hw : |(1179462083/5000000000 : ℝ)|=(1179462083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1179462037/5000000000 : ℝ)|^35 ≤ (96101784113/625000000000 : ℝ)^27
        have hw : |(-1179462037/5000000000 : ℝ)|=(1179462037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7531523147/10000000000 : ℝ)|^35 ≤ (69247428303003/100000000000000 : ℝ)^27
        have hw : |(7531523147/10000000000 : ℝ)|=(7531523147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1330705711/5000000000 : ℝ)*x 0 + (66687913/312500000 : ℝ)*x 1 + (3735094321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1330705711/5000000000 : ℝ)^35 ≤ (17979385159287/100000000000000 : ℝ)^27 := by
    have hnat : (1330705711 : ℕ)^35*100000000000000^27 ≤ 17979385159287^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330705711 5000000000 17979385159287 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66687913/312500000 : ℝ)^35 ≤ (1350332409281/10000000000000 : ℝ)^27 := by
    have hnat : (66687913 : ℕ)^35*10000000000000^27 ≤ 1350332409281^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66687913 312500000 1350332409281 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3735094321/5000000000 : ℝ)^35 ≤ (6851729074047/10000000000000 : ℝ)^27 := by
    have hnat : (3735094321 : ℕ)^35*10000000000000^27 ≤ 6851729074047^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735094321 5000000000 6851729074047 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1330705711/5000000000 : ℝ), (66687913/312500000 : ℝ), (3735094321/5000000000 : ℝ)] ![(17979385159287/100000000000000 : ℝ), (1350332409281/10000000000000 : ℝ), (6851729074047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1330705711/5000000000 : ℝ)|^35 ≤ (17979385159287/100000000000000 : ℝ)^27
        have hw : |(-1330705711/5000000000 : ℝ)|=(1330705711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66687913/312500000 : ℝ)|^35 ≤ (1350332409281/10000000000000 : ℝ)^27
        have hw : |(66687913/312500000 : ℝ)|=(66687913/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3735094321/5000000000 : ℝ)|^35 ≤ (6851729074047/10000000000000 : ℝ)^27
        have hw : |(3735094321/5000000000 : ℝ)|=(3735094321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (382577687/5000000000 : ℝ)*x 0 + (-62886867/1000000000 : ℝ)*x 1 + (9507006871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382577687/5000000000 : ℝ)^35 ≤ (1786400319053/50000000000000 : ℝ)^27 := by
    have hnat : (382577687 : ℕ)^35*50000000000000^27 ≤ 1786400319053^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382577687 5000000000 1786400319053 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62886867/1000000000 : ℝ)^35 ≤ (2770624845811/100000000000000 : ℝ)^27 := by
    have hnat : (62886867 : ℕ)^35*100000000000000^27 ≤ 2770624845811^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62886867 1000000000 2770624845811 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9507006871/10000000000 : ℝ)^35 ≤ (46828287248779/50000000000000 : ℝ)^27 := by
    have hnat : (9507006871 : ℕ)^35*50000000000000^27 ≤ 46828287248779^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9507006871 10000000000 46828287248779 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(382577687/5000000000 : ℝ), (-62886867/1000000000 : ℝ), (9507006871/10000000000 : ℝ)] ![(1786400319053/50000000000000 : ℝ), (2770624845811/100000000000000 : ℝ), (46828287248779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(382577687/5000000000 : ℝ)|^35 ≤ (1786400319053/50000000000000 : ℝ)^27
        have hw : |(382577687/5000000000 : ℝ)|=(382577687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62886867/1000000000 : ℝ)|^35 ≤ (2770624845811/100000000000000 : ℝ)^27
        have hw : |(-62886867/1000000000 : ℝ)|=(62886867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9507006871/10000000000 : ℝ)|^35 ≤ (46828287248779/50000000000000 : ℝ)^27
        have hw : |(9507006871/10000000000 : ℝ)|=(9507006871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1765426371/5000000000 : ℝ)*x 0 + (7900700187/10000000000 : ℝ)*x 1 + (-8558017/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765426371/5000000000 : ℝ)^35 ≤ (25936896366619/100000000000000 : ℝ)^27 := by
    have hnat : (1765426371 : ℕ)^35*100000000000000^27 ≤ 25936896366619^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765426371 5000000000 25936896366619 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7900700187/10000000000 : ℝ)^35 ≤ (73679093257779/100000000000000 : ℝ)^27 := by
    have hnat : (7900700187 : ℕ)^35*100000000000000^27 ≤ 73679093257779^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7900700187 10000000000 73679093257779 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8558017/625000000 : ℝ)^35 ≤ (96002590431/25000000000000 : ℝ)^27 := by
    have hnat : (8558017 : ℕ)^35*25000000000000^27 ≤ 96002590431^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8558017 625000000 96002590431 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1765426371/5000000000 : ℝ), (7900700187/10000000000 : ℝ), (-8558017/625000000 : ℝ)] ![(25936896366619/100000000000000 : ℝ), (73679093257779/100000000000000 : ℝ), (96002590431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1765426371/5000000000 : ℝ)|^35 ≤ (25936896366619/100000000000000 : ℝ)^27
        have hw : |(1765426371/5000000000 : ℝ)|=(1765426371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7900700187/10000000000 : ℝ)|^35 ≤ (73679093257779/100000000000000 : ℝ)^27
        have hw : |(7900700187/10000000000 : ℝ)|=(7900700187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8558017/625000000 : ℝ)|^35 ≤ (96002590431/25000000000000 : ℝ)^27
        have hw : |(-8558017/625000000 : ℝ)|=(8558017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1760442851/5000000000 : ℝ)*x 0 + (7883128901/10000000000 : ℝ)*x 1 + (215486961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1760442851/5000000000 : ℝ)^35 ≤ (12921013379643/50000000000000 : ℝ)^27 := by
    have hnat : (1760442851 : ℕ)^35*50000000000000^27 ≤ 12921013379643^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760442851 5000000000 12921013379643 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7883128901/10000000000 : ℝ)^35 ≤ (7346674762801/10000000000000 : ℝ)^27 := by
    have hnat : (7883128901 : ℕ)^35*10000000000000^27 ≤ 7346674762801^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7883128901 10000000000 7346674762801 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215486961/10000000000 : ℝ)^35 ≤ (172806398389/25000000000000 : ℝ)^27 := by
    have hnat : (215486961 : ℕ)^35*25000000000000^27 ≤ 172806398389^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215486961 10000000000 172806398389 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1760442851/5000000000 : ℝ), (7883128901/10000000000 : ℝ), (215486961/10000000000 : ℝ)] ![(12921013379643/50000000000000 : ℝ), (7346674762801/10000000000000 : ℝ), (172806398389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1760442851/5000000000 : ℝ)|^35 ≤ (12921013379643/50000000000000 : ℝ)^27
        have hw : |(1760442851/5000000000 : ℝ)|=(1760442851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7883128901/10000000000 : ℝ)|^35 ≤ (7346674762801/10000000000000 : ℝ)^27
        have hw : |(7883128901/10000000000 : ℝ)|=(7883128901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215486961/10000000000 : ℝ)|^35 ≤ (172806398389/25000000000000 : ℝ)^27
        have hw : |(215486961/10000000000 : ℝ)|=(215486961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-268622583/1250000000 : ℝ)*x 0 + (529474109/2000000000 : ℝ)*x 1 + (7470185677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268622583/1250000000 : ℝ)^35 ≤ (13626222404139/100000000000000 : ℝ)^27 := by
    have hnat : (268622583 : ℕ)^35*100000000000000^27 ≤ 13626222404139^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268622583 1250000000 13626222404139 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529474109/2000000000 : ℝ)^35 ≤ (17856522095513/100000000000000 : ℝ)^27 := by
    have hnat : (529474109 : ℕ)^35*100000000000000^27 ≤ 17856522095513^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529474109 2000000000 17856522095513 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7470185677/10000000000 : ℝ)^35 ≤ (1370345109747/2000000000000 : ℝ)^27 := by
    have hnat : (7470185677 : ℕ)^35*2000000000000^27 ≤ 1370345109747^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7470185677 10000000000 1370345109747 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268622583/1250000000 : ℝ), (529474109/2000000000 : ℝ), (7470185677/10000000000 : ℝ)] ![(13626222404139/100000000000000 : ℝ), (17856522095513/100000000000000 : ℝ), (1370345109747/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268622583/1250000000 : ℝ)|^35 ≤ (13626222404139/100000000000000 : ℝ)^27
        have hw : |(-268622583/1250000000 : ℝ)|=(268622583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529474109/2000000000 : ℝ)|^35 ≤ (17856522095513/100000000000000 : ℝ)^27
        have hw : |(529474109/2000000000 : ℝ)|=(529474109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7470185677/10000000000 : ℝ)|^35 ≤ (1370345109747/2000000000000 : ℝ)^27
        have hw : |(7470185677/10000000000 : ℝ)|=(7470185677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (614760321/10000000000 : ℝ)*x 0 + (-389700833/5000000000 : ℝ)*x 1 + (9506524277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (614760321/10000000000 : ℝ)^35 ≤ (2690319453601/100000000000000 : ℝ)^27 := by
    have hnat : (614760321 : ℕ)^35*100000000000000^27 ≤ 2690319453601^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614760321 10000000000 2690319453601 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389700833/5000000000 : ℝ)^35 ≤ (1829634415257/50000000000000 : ℝ)^27 := by
    have hnat : (389700833 : ℕ)^35*50000000000000^27 ≤ 1829634415257^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389700833 5000000000 1829634415257 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9506524277/10000000000 : ℝ)^35 ≤ (93650411707209/100000000000000 : ℝ)^27 := by
    have hnat : (9506524277 : ℕ)^35*100000000000000^27 ≤ 93650411707209^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9506524277 10000000000 93650411707209 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(614760321/10000000000 : ℝ), (-389700833/5000000000 : ℝ), (9506524277/10000000000 : ℝ)] ![(2690319453601/100000000000000 : ℝ), (1829634415257/50000000000000 : ℝ), (93650411707209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(614760321/10000000000 : ℝ)|^35 ≤ (2690319453601/100000000000000 : ℝ)^27
        have hw : |(614760321/10000000000 : ℝ)|=(614760321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389700833/5000000000 : ℝ)|^35 ≤ (1829634415257/50000000000000 : ℝ)^27
        have hw : |(-389700833/5000000000 : ℝ)|=(389700833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9506524277/10000000000 : ℝ)|^35 ≤ (93650411707209/100000000000000 : ℝ)^27
        have hw : |(9506524277/10000000000 : ℝ)|=(9506524277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3950636421/5000000000 : ℝ)*x 0 + (3532118093/10000000000 : ℝ)*x 1 + (-26335879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3950636421/5000000000 : ℝ)^35 ≤ (73686016040347/100000000000000 : ℝ)^27 := by
    have hnat : (3950636421 : ℕ)^35*100000000000000^27 ≤ 73686016040347^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3950636421 5000000000 73686016040347 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3532118093/10000000000 : ℝ)^35 ≤ (3243618260113/12500000000000 : ℝ)^27 := by
    have hnat : (3532118093 : ℕ)^35*12500000000000^27 ≤ 3243618260113^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3532118093 10000000000 3243618260113 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26335879/2000000000 : ℝ)^35 ≤ (365037866983/100000000000000 : ℝ)^27 := by
    have hnat : (26335879 : ℕ)^35*100000000000000^27 ≤ 365037866983^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26335879 2000000000 365037866983 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3950636421/5000000000 : ℝ), (3532118093/10000000000 : ℝ), (-26335879/2000000000 : ℝ)] ![(73686016040347/100000000000000 : ℝ), (3243618260113/12500000000000 : ℝ), (365037866983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3950636421/5000000000 : ℝ)|^35 ≤ (73686016040347/100000000000000 : ℝ)^27
        have hw : |(3950636421/5000000000 : ℝ)|=(3950636421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3532118093/10000000000 : ℝ)|^35 ≤ (3243618260113/12500000000000 : ℝ)^27
        have hw : |(3532118093/10000000000 : ℝ)|=(3532118093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26335879/2000000000 : ℝ)|^35 ≤ (365037866983/100000000000000 : ℝ)^27
        have hw : |(-26335879/2000000000 : ℝ)|=(26335879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7880845683/10000000000 : ℝ)*x 0 + (352052917/1000000000 : ℝ)*x 1 + (222898453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7880845683/10000000000 : ℝ)^35 ≤ (3671958283131/5000000000000 : ℝ)^27 := by
    have hnat : (7880845683 : ℕ)^35*5000000000000^27 ≤ 3671958283131^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7880845683 10000000000 3671958283131 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352052917/1000000000 : ℝ)^35 ≤ (25838634641491/100000000000000 : ℝ)^27 := by
    have hnat : (352052917 : ℕ)^35*100000000000000^27 ≤ 25838634641491^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352052917 1000000000 25838634641491 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222898453/10000000000 : ℝ)^35 ≤ (722199681631/100000000000000 : ℝ)^27 := by
    have hnat : (222898453 : ℕ)^35*100000000000000^27 ≤ 722199681631^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222898453 10000000000 722199681631 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7880845683/10000000000 : ℝ), (352052917/1000000000 : ℝ), (222898453/10000000000 : ℝ)] ![(3671958283131/5000000000000 : ℝ), (25838634641491/100000000000000 : ℝ), (722199681631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7880845683/10000000000 : ℝ)|^35 ≤ (3671958283131/5000000000000 : ℝ)^27
        have hw : |(7880845683/10000000000 : ℝ)|=(7880845683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352052917/1000000000 : ℝ)|^35 ≤ (25838634641491/100000000000000 : ℝ)^27
        have hw : |(352052917/1000000000 : ℝ)|=(352052917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(222898453/10000000000 : ℝ)|^35 ≤ (722199681631/100000000000000 : ℝ)^27
        have hw : |(222898453/10000000000 : ℝ)|=(222898453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2559588447/5000000000 : ℝ)*x 0 + (2498368921/10000000000 : ℝ)*x 1 + (1267459681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2559588447/5000000000 : ℝ)^35 ≤ (327964808223/781250000000 : ℝ)^27 := by
    have hnat : (2559588447 : ℕ)^35*781250000000^27 ≤ 327964808223^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559588447 5000000000 327964808223 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498368921/10000000000 : ℝ)^35 ≤ (4141183258737/25000000000000 : ℝ)^27 := by
    have hnat : (2498368921 : ℕ)^35*25000000000000^27 ≤ 4141183258737^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498368921 10000000000 4141183258737 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267459681/2500000000 : ℝ)^35 ≤ (1295492859271/3125000000000 : ℝ)^27 := by
    have hnat : (1267459681 : ℕ)^35*3125000000000^27 ≤ 1295492859271^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267459681 2500000000 1295492859271 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2559588447/5000000000 : ℝ), (2498368921/10000000000 : ℝ), (1267459681/2500000000 : ℝ)] ![(327964808223/781250000000 : ℝ), (4141183258737/25000000000000 : ℝ), (1295492859271/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2559588447/5000000000 : ℝ)|^35 ≤ (327964808223/781250000000 : ℝ)^27
        have hw : |(-2559588447/5000000000 : ℝ)|=(2559588447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498368921/10000000000 : ℝ)|^35 ≤ (4141183258737/25000000000000 : ℝ)^27
        have hw : |(2498368921/10000000000 : ℝ)|=(2498368921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1267459681/2500000000 : ℝ)|^35 ≤ (1295492859271/3125000000000 : ℝ)^27
        have hw : |(1267459681/2500000000 : ℝ)|=(1267459681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (513497649/5000000000 : ℝ)*x 0 + (-3647802917/10000000000 : ℝ)*x 1 + (7402338513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513497649/5000000000 : ℝ)^35 ≤ (654048362037/12500000000000 : ℝ)^27 := by
    have hnat : (513497649 : ℕ)^35*12500000000000^27 ≤ 654048362037^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513497649 5000000000 654048362037 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3647802917/10000000000 : ℝ)^35 ≤ (27055955890671/100000000000000 : ℝ)^27 := by
    have hnat : (3647802917 : ℕ)^35*100000000000000^27 ≤ 27055955890671^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3647802917 10000000000 27055955890671 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7402338513/10000000000 : ℝ)^35 ≤ (67711657197417/100000000000000 : ℝ)^27 := by
    have hnat : (7402338513 : ℕ)^35*100000000000000^27 ≤ 67711657197417^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7402338513 10000000000 67711657197417 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(513497649/5000000000 : ℝ), (-3647802917/10000000000 : ℝ), (7402338513/10000000000 : ℝ)] ![(654048362037/12500000000000 : ℝ), (27055955890671/100000000000000 : ℝ), (67711657197417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(513497649/5000000000 : ℝ)|^35 ≤ (654048362037/12500000000000 : ℝ)^27
        have hw : |(513497649/5000000000 : ℝ)|=(513497649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3647802917/10000000000 : ℝ)|^35 ≤ (27055955890671/100000000000000 : ℝ)^27
        have hw : |(-3647802917/10000000000 : ℝ)|=(3647802917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7402338513/10000000000 : ℝ)|^35 ≤ (67711657197417/100000000000000 : ℝ)^27
        have hw : |(7402338513/10000000000 : ℝ)|=(7402338513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308049_s0_s0_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (730423719/1250000000 : ℝ)*x 0 + (584339081/1000000000 : ℝ)*x 1 + (-122202969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730423719/1250000000 : ℝ)^35 ≤ (49834317541839/100000000000000 : ℝ)^27 := by
    have hnat : (730423719 : ℕ)^35*100000000000000^27 ≤ 49834317541839^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730423719 1250000000 49834317541839 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584339081/1000000000 : ℝ)^35 ≤ (49834329238277/100000000000000 : ℝ)^27 := by
    have hnat : (584339081 : ℕ)^35*100000000000000^27 ≤ 49834329238277^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584339081 1000000000 49834329238277 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122202969/10000000000 : ℝ)^35 ≤ (66270639701/20000000000000 : ℝ)^27 := by
    have hnat : (122202969 : ℕ)^35*20000000000000^27 ≤ 66270639701^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122202969 10000000000 66270639701 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(730423719/1250000000 : ℝ), (584339081/1000000000 : ℝ), (-122202969/10000000000 : ℝ)] ![(49834317541839/100000000000000 : ℝ), (49834329238277/100000000000000 : ℝ), (66270639701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(730423719/1250000000 : ℝ)|^35 ≤ (49834317541839/100000000000000 : ℝ)^27
        have hw : |(730423719/1250000000 : ℝ)|=(730423719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(584339081/1000000000 : ℝ)|^35 ≤ (49834329238277/100000000000000 : ℝ)^27
        have hw : |(584339081/1000000000 : ℝ)|=(584339081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122202969/10000000000 : ℝ)|^35 ≤ (66270639701/20000000000000 : ℝ)^27
        have hw : |(-122202969/10000000000 : ℝ)|=(122202969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308049_s0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : (0 : ℝ) ≤ ((84739/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84739/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16949/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16949/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2787/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2787/12500 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3470187827/10000000000 : ℝ)*X 0 0+(867546923/2500000000 : ℝ)*X 0 1+(1158611551/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1179462083/5000000000 : ℝ)*X 1 0+(-1179462037/5000000000 : ℝ)*X 1 1+(7531523147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1330705711/5000000000 : ℝ)*X 0 0+(66687913/312500000 : ℝ)*X 0 1+(3735094321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((382577687/5000000000 : ℝ)*X 1 0+(-62886867/1000000000 : ℝ)*X 1 1+(9507006871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1765426371/5000000000 : ℝ)*X 2 0+(7900700187/10000000000 : ℝ)*X 2 1+(-8558017/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1760442851/5000000000 : ℝ)*X 0 0+(7883128901/10000000000 : ℝ)*X 0 1+(215486961/10000000000 : ℝ)*X 0 2+(1760442851/5000000000 : ℝ)*X 1 0+(7883128901/10000000000 : ℝ)*X 1 1+(215486961/10000000000 : ℝ)*X 1 2+(1760442851/5000000000 : ℝ)*X 2 0+(7883128901/10000000000 : ℝ)*X 2 1+(215486961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-268622583/1250000000 : ℝ)*X 0 0+(529474109/2000000000 : ℝ)*X 0 1+(7470185677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((614760321/10000000000 : ℝ)*X 1 0+(-389700833/5000000000 : ℝ)*X 1 1+(9506524277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3950636421/5000000000 : ℝ)*X 2 0+(3532118093/10000000000 : ℝ)*X 2 1+(-26335879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7880845683/10000000000 : ℝ)*X 0 0+(352052917/1000000000 : ℝ)*X 0 1+(222898453/10000000000 : ℝ)*X 0 2+(7880845683/10000000000 : ℝ)*X 1 0+(352052917/1000000000 : ℝ)*X 1 1+(222898453/10000000000 : ℝ)*X 1 2+(7880845683/10000000000 : ℝ)*X 2 0+(352052917/1000000000 : ℝ)*X 2 1+(222898453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2559588447/5000000000 : ℝ)*X 0 0+(2498368921/10000000000 : ℝ)*X 0 1+(1267459681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((513497649/5000000000 : ℝ)*X 1 0+(-3647802917/10000000000 : ℝ)*X 1 1+(7402338513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((730423719/1250000000 : ℝ)*X 2 0+(584339081/1000000000 : ℝ)*X 2 1+(-122202969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308049_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((84739/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84739/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11547281420002287/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (2872066153/10000000000 : ℝ)*(base5) + (662720656541/1000000000000 : ℝ)*(base7) + (33268196251/1000000000000 : ℝ)*(base60) + (198739846577/100000000000 : ℝ)*(major_s0_0) + (198739846577/100000000000 : ℝ)*(major_s0_1) + (198739846577/100000000000 : ℝ)*(major_s0_2) + (104189/31250000000 : ℝ)*(sp_s0_0) + (443897/125000000000 : ℝ)*(sp_s0_1) + (45990048589/20000000000 : ℝ)*(sp_s0_7) + (1149704056957/500000000000 : ℝ)*(sp_s0_8) + (161671099439/62500000000 : ℝ)*(sp_s0_9) + (1643707381703/1000000000000 : ℝ)*(sp_s0_13) + (12606113/500000000000 : ℝ)*(sp_s0_14) + (23862127/200000000000 : ℝ)*(sp_s0_15) + (1268193340461/1000000000000 : ℝ)*(f.failure) + (574882743931/250000000000 : ℝ)*(f.sum) + (3007650423/5000000000000000000000 : ℝ)*base62 + (3280907998151/125000000000000000000000000 : ℝ)*base64 + (6146917198151/125000000000000000000000000 : ℝ)*base66 + (771422840497129/1000000000000000000000000000 : ℝ)*base68 + (162757327211921/1000000000000000000000000000 : ℝ)*base71 + (116168647414349/125000000000000000000000000 : ℝ)*base72 + (340568730202871/1000000000000000000000000000 : ℝ)*base74 + (509580887902871/1000000000000000000000000000 : ℝ)*base76 + (17488811/2000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (16229/100000000000000000 : ℝ)*base86 + (16229/100000000000000000 : ℝ)*base88 + (16229/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16949/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16949/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (135323486053520958711/19531250000000000000000000 : ℝ) := by norm_num
    linear_combination (359225733683/1000000000000 : ℝ)*(base5) + (662069615721/1000000000000 : ℝ)*(base7) + (12799882583/50000000000 : ℝ)*(base60) + (497021682529/250000000000 : ℝ)*(major_s0_0) + (497021682529/250000000000 : ℝ)*(major_s0_1) + (497021682529/250000000000 : ℝ)*(major_s0_2) + (263267/100000000000 : ℝ)*(sp_s0_0) + (2829111/1000000000000 : ℝ)*(sp_s0_1) + (516219/20000000000 : ℝ)*(sp_s0_7) + (65542703/1000000000000 : ℝ)*(sp_s0_8) + (2300840532479/1000000000000 : ℝ)*(sp_s0_14) + (575200151071/250000000000 : ℝ)*(sp_s0_15) + (2660094709781/1000000000000 : ℝ)*(sp_s0_16) + (314295283177/200000000000 : ℝ)*(sp_s0_20) + (634316266923/500000000000 : ℝ)*(f.failure) + (1150434488049/500000000000 : ℝ)*(f.sum) + (2250709409/10000000000000000000000 : ℝ)*base62 + (27226717820677/312500000000000000000000000 : ℝ)*base64 + (110239392601927/312500000000000000000000000 : ℝ)*base66 + (593766805638633/2500000000000000000000000000 : ℝ)*base68 + (183723862926783/2500000000000000000000000000 : ℝ)*base70 + (143567888195677/312500000000000000000000000 : ℝ)*base73 + (425174200361367/2500000000000000000000000000 : ℝ)*base74 + (288303043138633/2500000000000000000000000000 : ℝ)*base77 + (8846341/1000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (29747/50000000000000000 : ℝ)*base86 + (29747/50000000000000000 : ℝ)*base88 + (29747/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2787/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2787/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5394954660745544768169/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (246474691299/250000000000 : ℝ)*(base5) + (27412249921/500000000000 : ℝ)*(base7) + (16746887/1000000000000 : ℝ)*(base16) + (18960359203/500000000000 : ℝ)*(base39) + (14768059951/200000000000 : ℝ)*(base49) + (399560625111/500000000000 : ℝ)*(base59) + (1459095791979/1000000000000 : ℝ)*(major_s0_0) + (1459095791979/1000000000000 : ℝ)*(major_s0_1) + (1459095791979/1000000000000 : ℝ)*(major_s0_2) + (23444487/500000000000 : ℝ)*(sp_s0_1) + (711767/1000000000000 : ℝ)*(sp_s0_16) + (1953439040507/1000000000000 : ℝ)*(sp_s0_21) + (390675080929/200000000000 : ℝ)*(sp_s0_22) + (183708568371/62500000000 : ℝ)*(sp_s0_23) + (465537132677/500000000000 : ℝ)*(f.failure) + (1953439040507/1000000000000 : ℝ)*(f.sum) + (482222629/5000000000000000000000 : ℝ)*base63 + (480750640264777/1250000000000000000000000000 : ℝ)*base64 + (138710594610223/1250000000000000000000000000 : ℝ)*base67 + (1912427383688717/10000000000000000000000000000 : ℝ)*base69 + (8499344911806933/10000000000000000000000000000 : ℝ)*base70 + (1179306014014777/1250000000000000000000000000 : ℝ)*base73 + (586992036311283/10000000000000000000000000000 : ℝ)*base75 + (2109839231311283/10000000000000000000000000000 : ℝ)*base77 + (5859036949/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (4653/50000000000000000 : ℝ)*base86 + (4653/50000000000000000 : ℝ)*base88 + (4653/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : (0 : ℝ) ≤ ((84739/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84739/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16949/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16949/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2787/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2787/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308049_s0 p hpa hpb X hX

#print axioms solution
