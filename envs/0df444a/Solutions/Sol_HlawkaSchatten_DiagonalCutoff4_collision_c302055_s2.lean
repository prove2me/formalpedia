-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:47.444989+00:00
-- url     : https://prove2.me/submissions/3a7ccd17-0f10-4237-888d-0b13fd799ddc

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
theorem collision_support_c302055_s2_s2_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-562653797/5000000000 : ℝ)*x 0 + (755710081/1250000000 : ℝ)*x 1 + (5290531227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (562653797/5000000000 : ℝ)^131 ≤ (2777035655753/50000000000000 : ℝ)^99 := by
    have hnat : (562653797 : ℕ)^131*50000000000000^99 ≤ 2777035655753^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562653797 5000000000 2777035655753 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (755710081/1250000000 : ℝ)^131 ≤ (25690421637279/50000000000000 : ℝ)^99 := by
    have hnat : (755710081 : ℕ)^131*50000000000000^99 ≤ 25690421637279^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755710081 1250000000 25690421637279 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5290531227/10000000000 : ℝ)^131 ≤ (21532542696601/50000000000000 : ℝ)^99 := by
    have hnat : (5290531227 : ℕ)^131*50000000000000^99 ≤ 21532542696601^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290531227 10000000000 21532542696601 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-562653797/5000000000 : ℝ), (755710081/1250000000 : ℝ), (5290531227/10000000000 : ℝ)] ![(2777035655753/50000000000000 : ℝ), (25690421637279/50000000000000 : ℝ), (21532542696601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-562653797/5000000000 : ℝ)|^131 ≤ (2777035655753/50000000000000 : ℝ)^99
        have hw : |(-562653797/5000000000 : ℝ)|=(562653797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(755710081/1250000000 : ℝ)|^131 ≤ (25690421637279/50000000000000 : ℝ)^99
        have hw : |(755710081/1250000000 : ℝ)|=(755710081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5290531227/10000000000 : ℝ)|^131 ≤ (21532542696601/50000000000000 : ℝ)^99
        have hw : |(5290531227/10000000000 : ℝ)|=(5290531227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3339208343/5000000000 : ℝ)*x 0 + (1909719071/5000000000 : ℝ)*x 1 + (2189832859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3339208343/5000000000 : ℝ)^131 ≤ (2930706509271/5000000000000 : ℝ)^99 := by
    have hnat : (3339208343 : ℕ)^131*5000000000000^99 ≤ 2930706509271^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3339208343 5000000000 2930706509271 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909719071/5000000000 : ℝ)^131 ≤ (13991304425773/50000000000000 : ℝ)^99 := by
    have hnat : (1909719071 : ℕ)^131*50000000000000^99 ≤ 13991304425773^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909719071 5000000000 13991304425773 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189832859/10000000000 : ℝ)^131 ≤ (3350815237757/25000000000000 : ℝ)^99 := by
    have hnat : (2189832859 : ℕ)^131*25000000000000^99 ≤ 3350815237757^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189832859 10000000000 3350815237757 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3339208343/5000000000 : ℝ), (1909719071/5000000000 : ℝ), (2189832859/10000000000 : ℝ)] ![(2930706509271/5000000000000 : ℝ), (13991304425773/50000000000000 : ℝ), (3350815237757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3339208343/5000000000 : ℝ)|^131 ≤ (2930706509271/5000000000000 : ℝ)^99
        have hw : |(3339208343/5000000000 : ℝ)|=(3339208343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1909719071/5000000000 : ℝ)|^131 ≤ (13991304425773/50000000000000 : ℝ)^99
        have hw : |(1909719071/5000000000 : ℝ)|=(1909719071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2189832859/10000000000 : ℝ)|^131 ≤ (3350815237757/25000000000000 : ℝ)^99
        have hw : |(2189832859/10000000000 : ℝ)|=(2189832859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1703126801/5000000000 : ℝ)*x 0 + (4395286769/10000000000 : ℝ)*x 1 + (5215086897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1703126801/5000000000 : ℝ)^131 ≤ (3006102557847/12500000000000 : ℝ)^99 := by
    have hnat : (1703126801 : ℕ)^131*12500000000000^99 ≤ 3006102557847^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703126801 5000000000 3006102557847 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4395286769/10000000000 : ℝ)^131 ≤ (16848418768189/50000000000000 : ℝ)^99 := by
    have hnat : (4395286769 : ℕ)^131*50000000000000^99 ≤ 16848418768189^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395286769 10000000000 16848418768189 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215086897/10000000000 : ℝ)^131 ≤ (1690173679683/4000000000000 : ℝ)^99 := by
    have hnat : (5215086897 : ℕ)^131*4000000000000^99 ≤ 1690173679683^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215086897 10000000000 1690173679683 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1703126801/5000000000 : ℝ), (4395286769/10000000000 : ℝ), (5215086897/10000000000 : ℝ)] ![(3006102557847/12500000000000 : ℝ), (16848418768189/50000000000000 : ℝ), (1690173679683/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1703126801/5000000000 : ℝ)|^131 ≤ (3006102557847/12500000000000 : ℝ)^99
        have hw : |(-1703126801/5000000000 : ℝ)|=(1703126801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4395286769/10000000000 : ℝ)|^131 ≤ (16848418768189/50000000000000 : ℝ)^99
        have hw : |(4395286769/10000000000 : ℝ)|=(4395286769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215086897/10000000000 : ℝ)|^131 ≤ (1690173679683/4000000000000 : ℝ)^99
        have hw : |(5215086897/10000000000 : ℝ)|=(5215086897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2295824691/10000000000 : ℝ)*x 0 + (181609/2500000000 : ℝ)*x 1 + (8901677711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295824691/10000000000 : ℝ)^131 ≤ (7134170184547/50000000000000 : ℝ)^99 := by
    have hnat : (2295824691 : ℕ)^131*50000000000000^99 ≤ 7134170184547^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295824691 10000000000 7134170184547 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181609/2500000000 : ℝ)^131 ≤ (333735623/100000000000000 : ℝ)^99 := by
    have hnat : (181609 : ℕ)^131*100000000000000^99 ≤ 333735623^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181609 2500000000 333735623 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8901677711/10000000000 : ℝ)^131 ≤ (85731325887521/100000000000000 : ℝ)^99 := by
    have hnat : (8901677711 : ℕ)^131*100000000000000^99 ≤ 85731325887521^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8901677711 10000000000 85731325887521 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2295824691/10000000000 : ℝ), (181609/2500000000 : ℝ), (8901677711/10000000000 : ℝ)] ![(7134170184547/50000000000000 : ℝ), (333735623/100000000000000 : ℝ), (85731325887521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2295824691/10000000000 : ℝ)|^131 ≤ (7134170184547/50000000000000 : ℝ)^99
        have hw : |(2295824691/10000000000 : ℝ)|=(2295824691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181609/2500000000 : ℝ)|^131 ≤ (333735623/100000000000000 : ℝ)^99
        have hw : |(181609/2500000000 : ℝ)|=(181609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8901677711/10000000000 : ℝ)|^131 ≤ (85731325887521/100000000000000 : ℝ)^99
        have hw : |(8901677711/10000000000 : ℝ)|=(8901677711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1984184207/10000000000 : ℝ)*x 0 + (8767626271/10000000000 : ℝ)*x 1 + (-912602669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984184207/10000000000 : ℝ)^131 ≤ (11763533208979/100000000000000 : ℝ)^99 := by
    have hnat : (1984184207 : ℕ)^131*100000000000000^99 ≤ 11763533208979^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984184207 10000000000 11763533208979 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8767626271/10000000000 : ℝ)^131 ≤ (42013577066039/50000000000000 : ℝ)^99 := by
    have hnat : (8767626271 : ℕ)^131*50000000000000^99 ≤ 42013577066039^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8767626271 10000000000 42013577066039 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912602669/10000000000 : ℝ)^131 ≤ (841862529279/20000000000000 : ℝ)^99 := by
    have hnat : (912602669 : ℕ)^131*20000000000000^99 ≤ 841862529279^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912602669 10000000000 841862529279 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1984184207/10000000000 : ℝ), (8767626271/10000000000 : ℝ), (-912602669/10000000000 : ℝ)] ![(11763533208979/100000000000000 : ℝ), (42013577066039/50000000000000 : ℝ), (841862529279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1984184207/10000000000 : ℝ)|^131 ≤ (11763533208979/100000000000000 : ℝ)^99
        have hw : |(1984184207/10000000000 : ℝ)|=(1984184207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8767626271/10000000000 : ℝ)|^131 ≤ (42013577066039/50000000000000 : ℝ)^99
        have hw : |(8767626271/10000000000 : ℝ)|=(8767626271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-912602669/10000000000 : ℝ)|^131 ≤ (841862529279/20000000000000 : ℝ)^99
        have hw : |(-912602669/10000000000 : ℝ)|=(912602669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3980577937/10000000000 : ℝ)*x 0 + (3662634223/5000000000 : ℝ)*x 1 + (56974789/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3980577937/10000000000 : ℝ)^131 ≤ (29555328460441/100000000000000 : ℝ)^99 := by
    have hnat : (3980577937 : ℕ)^131*100000000000000^99 ≤ 29555328460441^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980577937 10000000000 29555328460441 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3662634223/5000000000 : ℝ)^131 ≤ (66241497987427/100000000000000 : ℝ)^99 := by
    have hnat : (3662634223 : ℕ)^131*100000000000000^99 ≤ 66241497987427^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3662634223 5000000000 66241497987427 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56974789/625000000 : ℝ)^131 ≤ (525396691801/12500000000000 : ℝ)^99 := by
    have hnat : (56974789 : ℕ)^131*12500000000000^99 ≤ 525396691801^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56974789 625000000 525396691801 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3980577937/10000000000 : ℝ), (3662634223/5000000000 : ℝ), (56974789/625000000 : ℝ)] ![(29555328460441/100000000000000 : ℝ), (66241497987427/100000000000000 : ℝ), (525396691801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3980577937/10000000000 : ℝ)|^131 ≤ (29555328460441/100000000000000 : ℝ)^99
        have hw : |(3980577937/10000000000 : ℝ)|=(3980577937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3662634223/5000000000 : ℝ)|^131 ≤ (66241497987427/100000000000000 : ℝ)^99
        have hw : |(3662634223/5000000000 : ℝ)|=(3662634223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56974789/625000000 : ℝ)|^131 ≤ (525396691801/12500000000000 : ℝ)^99
        have hw : |(56974789/625000000 : ℝ)|=(56974789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012879899/10000000000 : ℝ)*x 0 + (943989121/2000000000 : ℝ)*x 1 + (6010158617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012879899/10000000000 : ℝ)^131 ≤ (2397834966647/20000000000000 : ℝ)^99 := by
    have hnat : (2012879899 : ℕ)^131*20000000000000^99 ≤ 2397834966647^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012879899 10000000000 2397834966647 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943989121/2000000000 : ℝ)^131 ≤ (18514538660537/50000000000000 : ℝ)^99 := by
    have hnat : (943989121 : ℕ)^131*50000000000000^99 ≤ 18514538660537^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943989121 2000000000 18514538660537 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6010158617/10000000000 : ℝ)^131 ≤ (50981747832577/100000000000000 : ℝ)^99 := by
    have hnat : (6010158617 : ℕ)^131*100000000000000^99 ≤ 50981747832577^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6010158617 10000000000 50981747832577 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012879899/10000000000 : ℝ), (943989121/2000000000 : ℝ), (6010158617/10000000000 : ℝ)] ![(2397834966647/20000000000000 : ℝ), (18514538660537/50000000000000 : ℝ), (50981747832577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012879899/10000000000 : ℝ)|^131 ≤ (2397834966647/20000000000000 : ℝ)^99
        have hw : |(-2012879899/10000000000 : ℝ)|=(2012879899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(943989121/2000000000 : ℝ)|^131 ≤ (18514538660537/50000000000000 : ℝ)^99
        have hw : |(943989121/2000000000 : ℝ)|=(943989121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6010158617/10000000000 : ℝ)|^131 ≤ (50981747832577/100000000000000 : ℝ)^99
        have hw : |(6010158617/10000000000 : ℝ)|=(6010158617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (33993853/250000000 : ℝ)*x 0 + (-20588413/5000000000 : ℝ)*x 1 + (94506117/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33993853/250000000 : ℝ)^131 ≤ (1783638255797/25000000000000 : ℝ)^99 := by
    have hnat : (33993853 : ℕ)^131*25000000000000^99 ≤ 1783638255797^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33993853 250000000 1783638255797 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20588413/5000000000 : ℝ)^131 ≤ (3488201593/5000000000000 : ℝ)^99 := by
    have hnat : (20588413 : ℕ)^131*5000000000000^99 ≤ 3488201593^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20588413 5000000000 3488201593 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94506117/100000000 : ℝ)^131 ≤ (46397841468207/50000000000000 : ℝ)^99 := by
    have hnat : (94506117 : ℕ)^131*50000000000000^99 ≤ 46397841468207^99*100000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94506117 100000000 46397841468207 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33993853/250000000 : ℝ), (-20588413/5000000000 : ℝ), (94506117/100000000 : ℝ)] ![(1783638255797/25000000000000 : ℝ), (3488201593/5000000000000 : ℝ), (46397841468207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33993853/250000000 : ℝ)|^131 ≤ (1783638255797/25000000000000 : ℝ)^99
        have hw : |(33993853/250000000 : ℝ)|=(33993853/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20588413/5000000000 : ℝ)|^131 ≤ (3488201593/5000000000000 : ℝ)^99
        have hw : |(-20588413/5000000000 : ℝ)|=(20588413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94506117/100000000 : ℝ)|^131 ≤ (46397841468207/50000000000000 : ℝ)^99
        have hw : |(94506117/100000000 : ℝ)|=(94506117/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1500472439/2000000000 : ℝ)*x 0 + (935454471/2500000000 : ℝ)*x 1 + (-235861953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1500472439/2000000000 : ℝ)^131 ≤ (68368805978421/100000000000000 : ℝ)^99 := by
    have hnat : (1500472439 : ℕ)^131*100000000000000^99 ≤ 68368805978421^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500472439 2000000000 68368805978421 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935454471/2500000000 : ℝ)^131 ≤ (5446520642799/20000000000000 : ℝ)^99 := by
    have hnat : (935454471 : ℕ)^131*20000000000000^99 ≤ 5446520642799^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935454471 2500000000 5446520642799 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235861953/2500000000 : ℝ)^131 ≤ (879718157973/20000000000000 : ℝ)^99 := by
    have hnat : (235861953 : ℕ)^131*20000000000000^99 ≤ 879718157973^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235861953 2500000000 879718157973 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1500472439/2000000000 : ℝ), (935454471/2500000000 : ℝ), (-235861953/2500000000 : ℝ)] ![(68368805978421/100000000000000 : ℝ), (5446520642799/20000000000000 : ℝ), (879718157973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1500472439/2000000000 : ℝ)|^131 ≤ (68368805978421/100000000000000 : ℝ)^99
        have hw : |(1500472439/2000000000 : ℝ)|=(1500472439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(935454471/2500000000 : ℝ)|^131 ≤ (5446520642799/20000000000000 : ℝ)^99
        have hw : |(935454471/2500000000 : ℝ)|=(935454471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235861953/2500000000 : ℝ)|^131 ≤ (879718157973/20000000000000 : ℝ)^99
        have hw : |(-235861953/2500000000 : ℝ)|=(235861953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4409612951/5000000000 : ℝ)*x 0 + (241220933/1250000000 : ℝ)*x 1 + (874662053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4409612951/5000000000 : ℝ)^131 ≤ (42341070550137/50000000000000 : ℝ)^99 := by
    have hnat : (4409612951 : ℕ)^131*50000000000000^99 ≤ 42341070550137^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409612951 5000000000 42341070550137 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241220933/1250000000 : ℝ)^131 ≤ (11338538906329/100000000000000 : ℝ)^99 := by
    have hnat : (241220933 : ℕ)^131*100000000000000^99 ≤ 11338538906329^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241220933 1250000000 11338538906329 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874662053/10000000000 : ℝ)^131 ≤ (1989659988697/50000000000000 : ℝ)^99 := by
    have hnat : (874662053 : ℕ)^131*50000000000000^99 ≤ 1989659988697^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874662053 10000000000 1989659988697 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4409612951/5000000000 : ℝ), (241220933/1250000000 : ℝ), (874662053/10000000000 : ℝ)] ![(42341070550137/50000000000000 : ℝ), (11338538906329/100000000000000 : ℝ), (1989659988697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4409612951/5000000000 : ℝ)|^131 ≤ (42341070550137/50000000000000 : ℝ)^99
        have hw : |(4409612951/5000000000 : ℝ)|=(4409612951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241220933/1250000000 : ℝ)|^131 ≤ (11338538906329/100000000000000 : ℝ)^99
        have hw : |(241220933/1250000000 : ℝ)|=(241220933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(874662053/10000000000 : ℝ)|^131 ≤ (1989659988697/50000000000000 : ℝ)^99
        have hw : |(874662053/10000000000 : ℝ)|=(874662053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1333041219/10000000000 : ℝ)*x 0 + (8220056507/10000000000 : ℝ)*x 1 + (2491125207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333041219/10000000000 : ℝ)^131 ≤ (6949678836413/100000000000000 : ℝ)^99 := by
    have hnat : (1333041219 : ℕ)^131*100000000000000^99 ≤ 6949678836413^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333041219 10000000000 6949678836413 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8220056507/10000000000 : ℝ)^131 ≤ (3857710136243/5000000000000 : ℝ)^99 := by
    have hnat : (8220056507 : ℕ)^131*5000000000000^99 ≤ 3857710136243^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8220056507 10000000000 3857710136243 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491125207/10000000000 : ℝ)^131 ≤ (1987014803191/12500000000000 : ℝ)^99 := by
    have hnat : (2491125207 : ℕ)^131*12500000000000^99 ≤ 1987014803191^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491125207 10000000000 1987014803191 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1333041219/10000000000 : ℝ), (8220056507/10000000000 : ℝ), (2491125207/10000000000 : ℝ)] ![(6949678836413/100000000000000 : ℝ), (3857710136243/5000000000000 : ℝ), (1987014803191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1333041219/10000000000 : ℝ)|^131 ≤ (6949678836413/100000000000000 : ℝ)^99
        have hw : |(-1333041219/10000000000 : ℝ)|=(1333041219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8220056507/10000000000 : ℝ)|^131 ≤ (3857710136243/5000000000000 : ℝ)^99
        have hw : |(8220056507/10000000000 : ℝ)|=(8220056507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491125207/10000000000 : ℝ)|^131 ≤ (1987014803191/12500000000000 : ℝ)^99
        have hw : |(2491125207/10000000000 : ℝ)|=(2491125207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1526633477/2000000000 : ℝ)*x 0 + (-13686681/10000000000 : ℝ)*x 1 + (402912157/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1526633477/2000000000 : ℝ)^131 ≤ (34975278855441/50000000000000 : ℝ)^99 := by
    have hnat : (1526633477 : ℕ)^131*50000000000000^99 ≤ 34975278855441^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526633477 2000000000 34975278855441 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13686681/10000000000 : ℝ)^131 ≤ (507583111/3125000000000 : ℝ)^99 := by
    have hnat : (13686681 : ℕ)^131*3125000000000^99 ≤ 507583111^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13686681 10000000000 507583111 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402912157/1000000000 : ℝ)^131 ≤ (30033199617251/100000000000000 : ℝ)^99 := by
    have hnat : (402912157 : ℕ)^131*100000000000000^99 ≤ 30033199617251^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402912157 1000000000 30033199617251 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1526633477/2000000000 : ℝ), (-13686681/10000000000 : ℝ), (402912157/1000000000 : ℝ)] ![(34975278855441/50000000000000 : ℝ), (507583111/3125000000000 : ℝ), (30033199617251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1526633477/2000000000 : ℝ)|^131 ≤ (34975278855441/50000000000000 : ℝ)^99
        have hw : |(1526633477/2000000000 : ℝ)|=(1526633477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13686681/10000000000 : ℝ)|^131 ≤ (507583111/3125000000000 : ℝ)^99
        have hw : |(-13686681/10000000000 : ℝ)|=(13686681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402912157/1000000000 : ℝ)|^131 ≤ (30033199617251/100000000000000 : ℝ)^99
        have hw : |(402912157/1000000000 : ℝ)|=(402912157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (24737757/200000000 : ℝ)*x 0 + (548694779/625000000 : ℝ)*x 1 + (-105792261/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24737757/200000000 : ℝ)^131 ≤ (3147111641781/50000000000000 : ℝ)^99 := by
    have hnat : (24737757 : ℕ)^131*50000000000000^99 ≤ 3147111641781^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24737757 200000000 3147111641781 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548694779/625000000 : ℝ)^131 ≤ (10521612363539/12500000000000 : ℝ)^99 := by
    have hnat : (548694779 : ℕ)^131*12500000000000^99 ≤ 10521612363539^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548694779 625000000 10521612363539 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105792261/625000000 : ℝ)^131 ≤ (4766438892327/50000000000000 : ℝ)^99 := by
    have hnat : (105792261 : ℕ)^131*50000000000000^99 ≤ 4766438892327^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105792261 625000000 4766438892327 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24737757/200000000 : ℝ), (548694779/625000000 : ℝ), (-105792261/625000000 : ℝ)] ![(3147111641781/50000000000000 : ℝ), (10521612363539/12500000000000 : ℝ), (4766438892327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24737757/200000000 : ℝ)|^131 ≤ (3147111641781/50000000000000 : ℝ)^99
        have hw : |(24737757/200000000 : ℝ)|=(24737757/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548694779/625000000 : ℝ)|^131 ≤ (10521612363539/12500000000000 : ℝ)^99
        have hw : |(548694779/625000000 : ℝ)|=(548694779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105792261/625000000 : ℝ)|^131 ≤ (4766438892327/50000000000000 : ℝ)^99
        have hw : |(-105792261/625000000 : ℝ)|=(105792261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s2_s2_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4222761749/5000000000 : ℝ)*x 0 + (2134508243/10000000000 : ℝ)*x 1 + (168916573/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4222761749/5000000000 : ℝ)^131 ≤ (3998341790393/5000000000000 : ℝ)^99 := by
    have hnat : (4222761749 : ℕ)^131*5000000000000^99 ≤ 3998341790393^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222761749 5000000000 3998341790393 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134508243/10000000000 : ℝ)^131 ≤ (1295702264309/10000000000000 : ℝ)^99 := by
    have hnat : (2134508243 : ℕ)^131*10000000000000^99 ≤ 1295702264309^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134508243 10000000000 1295702264309 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168916573/1250000000 : ℝ)^131 ≤ (353807076829/5000000000000 : ℝ)^99 := by
    have hnat : (168916573 : ℕ)^131*5000000000000^99 ≤ 353807076829^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168916573 1250000000 353807076829 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4222761749/5000000000 : ℝ), (2134508243/10000000000 : ℝ), (168916573/1250000000 : ℝ)] ![(3998341790393/5000000000000 : ℝ), (1295702264309/10000000000000 : ℝ), (353807076829/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4222761749/5000000000 : ℝ)|^131 ≤ (3998341790393/5000000000000 : ℝ)^99
        have hw : |(4222761749/5000000000 : ℝ)|=(4222761749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2134508243/10000000000 : ℝ)|^131 ≤ (1295702264309/10000000000000 : ℝ)^99
        have hw : |(2134508243/10000000000 : ℝ)|=(2134508243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168916573/1250000000 : ℝ)|^131 ≤ (353807076829/5000000000000 : ℝ)^99
        have hw : |(168916573/1250000000 : ℝ)|=(168916573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302055_s2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((5729/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5729/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45739/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45739/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44829/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((86761/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86761/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(85817/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10591/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10591/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s2_pow0 : (5729/6250 : ℝ) ^ (65/16 : ℝ) ≤ (70215443760929251627/100000000000000000000 : ℝ) := by
    have hpowers : (5729/6250 : ℝ)^65 ≤ (70215443760929251627/100000000000000000000 : ℝ)^16 := by
      have hnat : (5729 : ℕ)^65*100000000000000000000^16 ≤ 70215443760929251627^16*6250^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5729 6250 70215443760929251627 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5729/6250 : ℝ)) (X := (70215443760929251627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (170215443760929251627/100000000000000000000 : ℝ) ≤ (356214262696991/312500000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (170215443760929251627/100000000000000000000 : ℝ)^16 ≤ (356214262696991/312500000000000 : ℝ)^65 := by
      have hnat : (170215443760929251627 : ℕ)^16*312500000000000^65 ≤ 356214262696991^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        170215443760929251627 100000000000000000000 356214262696991 312500000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (356214262696991/312500000000000 : ℝ)) (X := (170215443760929251627/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (120215443760929251627/50000000000000000000 : ℝ) ≤ (496411928804413/400000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (120215443760929251627/50000000000000000000 : ℝ)^16 ≤ (496411928804413/400000000000000 : ℝ)^65 := by
      have hnat : (120215443760929251627 : ℕ)^16*400000000000000^65 ≤ 496411928804413^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120215443760929251627 50000000000000000000 496411928804413 400000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (496411928804413/400000000000000 : ℝ)) (X := (120215443760929251627/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(43714262696991/286450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1011441813806613/9166400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (5729/6250 : ℝ)) (alpha := (43714262696991/286450000000000 : ℝ)) (beta := (1011441813806613/9166400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5729/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(43714262696991/286450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1011441813806613/9166400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (45739/50000 : ℝ) ^ (65/16 : ℝ) ≤ (69638424204134873721/100000000000000000000 : ℝ) := by
    have hpowers : (45739/50000 : ℝ)^65 ≤ (69638424204134873721/100000000000000000000 : ℝ)^16 := by
      have hnat : (45739 : ℕ)^65*100000000000000000000^16 ≤ 69638424204134873721^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45739 50000 69638424204134873721 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45739/50000 : ℝ)) (X := (69638424204134873721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (169638424204134873721/100000000000000000000 : ℝ) ≤ (11389332499329737/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (169638424204134873721/100000000000000000000 : ℝ)^16 ≤ (11389332499329737/10000000000000000 : ℝ)^65 := by
      have hnat : (169638424204134873721 : ℕ)^16*10000000000000000^65 ≤ 11389332499329737^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        169638424204134873721 100000000000000000000 11389332499329737 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11389332499329737/10000000000000000 : ℝ)) (X := (169638424204134873721/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (119638424204134873721/50000000000000000000 : ℝ) ≤ (12395608743231317/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (119638424204134873721/50000000000000000000 : ℝ)^16 ≤ (12395608743231317/10000000000000000 : ℝ)^65 := by
      have hnat : (119638424204134873721 : ℕ)^16*10000000000000000^65 ≤ 12395608743231317^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119638424204134873721 50000000000000000000 12395608743231317 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12395608743231317/10000000000000000 : ℝ)) (X := (119638424204134873721/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1389332499329737/9147800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(50313812195079/457390000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (45739/50000 : ℝ)) (alpha := (1389332499329737/9147800000000000 : ℝ)) (beta := (50313812195079/457390000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (45739/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1389332499329737/9147800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(50313812195079/457390000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (44829/50000 : ℝ) ^ (65/16 : ℝ) ≤ (16044752101501946877/25000000000000000000 : ℝ) := by
    have hpowers : (44829/50000 : ℝ)^65 ≤ (16044752101501946877/25000000000000000000 : ℝ)^16 := by
      have hnat : (44829 : ℕ)^65*25000000000000000000^16 ≤ 16044752101501946877^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44829 50000 16044752101501946877 25000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44829/50000 : ℝ)) (X := (16044752101501946877/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (41044752101501946877/25000000000000000000 : ℝ) ≤ (353062249574049/312500000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (41044752101501946877/25000000000000000000 : ℝ)^16 ≤ (353062249574049/312500000000000 : ℝ)^65 := by
      have hnat : (41044752101501946877 : ℕ)^16*312500000000000^65 ≤ 353062249574049^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41044752101501946877 25000000000000000000 353062249574049 312500000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (353062249574049/312500000000000 : ℝ)) (X := (41044752101501946877/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (28544752101501946877/12500000000000000000 : ℝ) ≤ (12253912428388161/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (28544752101501946877/12500000000000000000 : ℝ)^16 ≤ (12253912428388161/10000000000000000 : ℝ)^65 := by
      have hnat : (28544752101501946877 : ℕ)^16*10000000000000000^65 ≤ 12253912428388161^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28544752101501946877 12500000000000000000 12253912428388161 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12253912428388161/10000000000000000 : ℝ)) (X := (28544752101501946877/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(40562249574049/280181250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(318640147339531/2988600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (44829/50000 : ℝ)) (alpha := (40562249574049/280181250000000 : ℝ)) (beta := (318640147339531/2988600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44829/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(40562249574049/280181250000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(318640147339531/2988600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-562653797/5000000000 : ℝ)*X 0 0+(755710081/1250000000 : ℝ)*X 0 1+(5290531227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3339208343/5000000000 : ℝ)*X 0 0+(1909719071/5000000000 : ℝ)*X 0 1+(2189832859/10000000000 : ℝ)*X 0 2+(3339208343/5000000000 : ℝ)*X 1 0+(1909719071/5000000000 : ℝ)*X 1 1+(2189832859/10000000000 : ℝ)*X 1 2+(3339208343/5000000000 : ℝ)*X 2 0+(1909719071/5000000000 : ℝ)*X 2 1+(2189832859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1703126801/5000000000 : ℝ)*X 0 0+(4395286769/10000000000 : ℝ)*X 0 1+(5215086897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2295824691/10000000000 : ℝ)*X 1 0+(181609/2500000000 : ℝ)*X 1 1+(8901677711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1984184207/10000000000 : ℝ)*X 2 0+(8767626271/10000000000 : ℝ)*X 2 1+(-912602669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3980577937/10000000000 : ℝ)*X 0 0+(3662634223/5000000000 : ℝ)*X 0 1+(56974789/625000000 : ℝ)*X 0 2+(3980577937/10000000000 : ℝ)*X 1 0+(3662634223/5000000000 : ℝ)*X 1 1+(56974789/625000000 : ℝ)*X 1 2+(3980577937/10000000000 : ℝ)*X 2 0+(3662634223/5000000000 : ℝ)*X 2 1+(56974789/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-2012879899/10000000000 : ℝ)*X 0 0+(943989121/2000000000 : ℝ)*X 0 1+(6010158617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((33993853/250000000 : ℝ)*X 1 0+(-20588413/5000000000 : ℝ)*X 1 1+(94506117/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1500472439/2000000000 : ℝ)*X 2 0+(935454471/2500000000 : ℝ)*X 2 1+(-235861953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((4409612951/5000000000 : ℝ)*X 0 0+(241220933/1250000000 : ℝ)*X 0 1+(874662053/10000000000 : ℝ)*X 0 2+(4409612951/5000000000 : ℝ)*X 1 0+(241220933/1250000000 : ℝ)*X 1 1+(874662053/10000000000 : ℝ)*X 1 2+(4409612951/5000000000 : ℝ)*X 2 0+(241220933/1250000000 : ℝ)*X 2 1+(874662053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1333041219/10000000000 : ℝ)*X 0 0+(8220056507/10000000000 : ℝ)*X 0 1+(2491125207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1526633477/2000000000 : ℝ)*X 1 0+(-13686681/10000000000 : ℝ)*X 1 1+(402912157/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((24737757/200000000 : ℝ)*X 2 0+(548694779/625000000 : ℝ)*X 2 1+(-105792261/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4222761749/5000000000 : ℝ)*X 0 0+(2134508243/10000000000 : ℝ)*X 0 1+(168916573/1250000000 : ℝ)*X 0 2+(4222761749/5000000000 : ℝ)*X 1 0+(2134508243/10000000000 : ℝ)*X 1 1+(168916573/1250000000 : ℝ)*X 1 2+(4222761749/5000000000 : ℝ)*X 2 0+(2134508243/10000000000 : ℝ)*X 2 1+(168916573/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((86761/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86761/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2175470145545338663533395848049/184265635639200000000000000000000000 : ℝ) := by norm_num
    linear_combination (704373973553/1000000000000 : ℝ)*(base7) + (1898591/250000000000 : ℝ)*(base23) + (268931/500000000000 : ℝ)*(base49) + (820272448477/1000000000000 : ℝ)*(base53) + (48403/31250000000 : ℝ)*(base60) + (1710188067371/1000000000000 : ℝ)*(major_s2_0) + (1710188067371/1000000000000 : ℝ)*(major_s2_1) + (444957809447/500000000000 : ℝ)*(major_s2_2) + (5146579/200000000000 : ℝ)*(sp_s2_0) + (102214036419/100000000000 : ℝ)*(sp_s2_7) + (511083149513/500000000000 : ℝ)*(sp_s2_8) + (921215576569/500000000000 : ℝ)*(sp_s2_9) + (925421573949/500000000000 : ℝ)*(sp_s2_13) + (10097/50000000000 : ℝ)*(sp_s2_21) + (229293834869/200000000000 : ℝ)*(f.failure) + (921219373751/500000000000 : ℝ)*(f.sum) + (4838291686983452503/24122748600000000000000000000000 : ℝ)*base63 + (63349551088201/87900000000000000000000000 : ℝ)*base65 + (15393849031881/228695000000000000000000000 : ℝ)*base66 + (994205435041/2060156250000000000000000 : ℝ)*base69 + (52880876886589307/503579100000000000000000000000 : ℝ)*base71 + (2274170350019897/9166400000000000000000000000 : ℝ)*base72 + (4841721896989667/9147800000000000000000000000 : ℝ)*base75 + (248664182498291/286450000000000000000000000 : ℝ)*base77 + (157346457156386406963/419261969600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1127/2000000000000000 : ℝ)*base86 + (1127/2000000000000000 : ℝ)*base88 + (1127/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(85817/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (302632879685702111464329060931/61421878546400000000000000000000000 : ℝ) := by norm_num
    linear_combination (146258912557/200000000000 : ℝ)*(base7) + (950049/250000000000 : ℝ)*(base34) + (321153567099/500000000000 : ℝ)*(base53) + (1581974845899/1000000000000 : ℝ)*(major_s2_0) + (316395729219/200000000000 : ℝ)*(major_s2_1) + (939671511897/1000000000000 : ℝ)*(major_s2_2) + (48615117/1000000000000 : ℝ)*(sp_s2_0) + (8787877/1000000000000 : ℝ)*(sp_s2_7) + (20290623/250000000000 : ℝ)*(sp_s2_8) + (40524487321/40000000000 : ℝ)*(sp_s2_14) + (253273055931/250000000000 : ℝ)*(sp_s2_15) + (827740260207/500000000000 : ℝ)*(sp_s2_16) + (358358225191/200000000000 : ℝ)*(sp_s2_20) + (3169/156250000 : ℝ)*(sp_s2_27) + (530260322483/500000000000 : ℝ)*(f.failure) + (827740260207/500000000000 : ℝ)*(f.sum) + (20546069866672499827/136695575400000000000000000000000 : ℝ)*base62 + (132974192869111/996200000000000000000000000 : ℝ)*base64 + (154056289921843/457390000000000000000000000 : ℝ)*base67 + (73204331471561/373575000000000000000000000 : ℝ)*base68 + (7441388294877019/335719400000000000000000000000 : ℝ)*base70 + (1591068809243193/9166400000000000000000000000 : ℝ)*base72 + (140472136169237/1829560000000000000000000000 : ℝ)*base74 + (89448983476011/286450000000000000000000000 : ℝ)*base76 + (421695569410719027/419261969600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (3911/5000000000000000 : ℝ)*base87 + (3911/5000000000000000 : ℝ)*base89 + (3911/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10591/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10591/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (243542646080427761505374204551/46066408909800000000000000000000000 : ℝ) := by norm_num
    linear_combination (854947589093/1000000000000 : ℝ)*(base7) + (32977462387/125000000000 : ℝ)*(base43) + (10419990097/1000000000000 : ℝ)*(base50) + (388304410567/250000000000 : ℝ)*(major_s2_0) + (322349485793/250000000000 : ℝ)*(major_s2_1) + (388304410567/250000000000 : ℝ)*(major_s2_2) + (10953353/1000000000000 : ℝ)*(sp_s2_6) + (869383/1000000000000 : ℝ)*(sp_s2_7) + (3802461/125000000000 : ℝ)*(sp_s2_9) + (60613719/1000000000000 : ℝ)*(sp_s2_20) + (1277674852163/1000000000000 : ℝ)*(sp_s2_21) + (770747710321/500000000000 : ℝ)*(sp_s2_22) + (638822650929/500000000000 : ℝ)*(sp_s2_23) + (474028994489/250000000000 : ℝ)*(sp_s2_27) + (208247991187/200000000000 : ℝ)*(f.failure) + (770747710321/500000000000 : ℝ)*(f.sum) + (28320938745308831891/51260840775000000000000000000000 : ℝ)*base62 + (165608893483793/747150000000000000000000000 : ℝ)*base64 + (78058268284071/228695000000000000000000000 : ℝ)*base67 + (591561061384637/1120725000000000000000000000 : ℝ)*base68 + (143466062075767/14811150000000000000000000000 : ℝ)*base70 + (362056730705091/2291600000000000000000000000 : ℝ)*base73 + (587408988921059/2286950000000000000000000000 : ℝ)*base74 + (15697361121431/143225000000000000000000000 : ℝ)*base76 + (491175893925443969/104815492400000000000000000000000 : ℝ)*base79 + (479/2000000000000000 : ℝ)*base87 + (479/2000000000000000 : ℝ)*base89 + (479/2000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((5729/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5729/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45739/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45739/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44829/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((86761/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86761/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(85817/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10591/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10591/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302055_s2 p hpa hpb X hX hprev1

#print axioms solution
