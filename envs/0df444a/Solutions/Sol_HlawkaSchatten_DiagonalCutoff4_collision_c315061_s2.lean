-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315061_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:56:11.628924+00:00
-- url     : https://prove2.me/submissions/66e540cc-acda-4c5e-a389-f50e9a33ff16

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
theorem collision_support_c315061_s2_s2_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062095827/10000000000 : ℝ)*x 0 + (2238200049/5000000000 : ℝ)*x 1 + (5816320681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062095827/10000000000 : ℝ)^19 ≤ (13534987788477/100000000000000 : ℝ)^15 := by
    have hnat : (2062095827 : ℕ)^19*100000000000000^15 ≤ 13534987788477^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062095827 10000000000 13534987788477 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238200049/5000000000 : ℝ)^19 ≤ (36127945824077/100000000000000 : ℝ)^15 := by
    have hnat : (2238200049 : ℕ)^19*100000000000000^15 ≤ 36127945824077^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238200049 5000000000 36127945824077 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5816320681/10000000000 : ℝ)^19 ≤ (50337066369577/100000000000000 : ℝ)^15 := by
    have hnat : (5816320681 : ℕ)^19*100000000000000^15 ≤ 50337066369577^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5816320681 10000000000 50337066369577 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062095827/10000000000 : ℝ), (2238200049/5000000000 : ℝ), (5816320681/10000000000 : ℝ)] ![(13534987788477/100000000000000 : ℝ), (36127945824077/100000000000000 : ℝ), (50337066369577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062095827/10000000000 : ℝ)|^19 ≤ (13534987788477/100000000000000 : ℝ)^15
        have hw : |(-2062095827/10000000000 : ℝ)|=(2062095827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238200049/5000000000 : ℝ)|^19 ≤ (36127945824077/100000000000000 : ℝ)^15
        have hw : |(2238200049/5000000000 : ℝ)|=(2238200049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5816320681/10000000000 : ℝ)|^19 ≤ (50337066369577/100000000000000 : ℝ)^15
        have hw : |(5816320681/10000000000 : ℝ)|=(5816320681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4671242571/10000000000 : ℝ)*x 0 + (-2100680353/10000000000 : ℝ)*x 1 + (2801594487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4671242571/10000000000 : ℝ)^19 ≤ (3813125203801/10000000000000 : ℝ)^15 := by
    have hnat : (4671242571 : ℕ)^19*10000000000000^15 ≤ 3813125203801^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671242571 10000000000 3813125203801 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100680353/10000000000 : ℝ)^19 ≤ (216509019193/1562500000000 : ℝ)^15 := by
    have hnat : (2100680353 : ℕ)^19*1562500000000^15 ≤ 216509019193^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100680353 10000000000 216509019193 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2801594487/5000000000 : ℝ)^19 ≤ (2400608536349/5000000000000 : ℝ)^15 := by
    have hnat : (2801594487 : ℕ)^19*5000000000000^15 ≤ 2400608536349^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801594487 5000000000 2400608536349 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4671242571/10000000000 : ℝ), (-2100680353/10000000000 : ℝ), (2801594487/5000000000 : ℝ)] ![(3813125203801/10000000000000 : ℝ), (216509019193/1562500000000 : ℝ), (2400608536349/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4671242571/10000000000 : ℝ)|^19 ≤ (3813125203801/10000000000000 : ℝ)^15
        have hw : |(4671242571/10000000000 : ℝ)|=(4671242571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100680353/10000000000 : ℝ)|^19 ≤ (216509019193/1562500000000 : ℝ)^15
        have hw : |(-2100680353/10000000000 : ℝ)|=(2100680353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2801594487/5000000000 : ℝ)|^19 ≤ (2400608536349/5000000000000 : ℝ)^15
        have hw : |(2801594487/5000000000 : ℝ)|=(2801594487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4731454493/10000000000 : ℝ)*x 0 + (3110634827/5000000000 : ℝ)*x 1 + (-1145579217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4731454493/10000000000 : ℝ)^19 ≤ (38754896262531/100000000000000 : ℝ)^15 := by
    have hnat : (4731454493 : ℕ)^19*100000000000000^15 ≤ 38754896262531^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4731454493 10000000000 38754896262531 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110634827/5000000000 : ℝ)^19 ≤ (27408384422933/50000000000000 : ℝ)^15 := by
    have hnat : (3110634827 : ℕ)^19*50000000000000^15 ≤ 27408384422933^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110634827 5000000000 27408384422933 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145579217/10000000000 : ℝ)^19 ≤ (3214167440653/50000000000000 : ℝ)^15 := by
    have hnat : (1145579217 : ℕ)^19*50000000000000^15 ≤ 3214167440653^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145579217 10000000000 3214167440653 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4731454493/10000000000 : ℝ), (3110634827/5000000000 : ℝ), (-1145579217/10000000000 : ℝ)] ![(38754896262531/100000000000000 : ℝ), (27408384422933/50000000000000 : ℝ), (3214167440653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4731454493/10000000000 : ℝ)|^19 ≤ (38754896262531/100000000000000 : ℝ)^15
        have hw : |(4731454493/10000000000 : ℝ)|=(4731454493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3110634827/5000000000 : ℝ)|^19 ≤ (27408384422933/50000000000000 : ℝ)^15
        have hw : |(3110634827/5000000000 : ℝ)|=(3110634827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1145579217/10000000000 : ℝ)|^19 ≤ (3214167440653/50000000000000 : ℝ)^15
        have hw : |(-1145579217/10000000000 : ℝ)|=(1145579217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3085016781/5000000000 : ℝ)*x 0 + (2824541799/10000000000 : ℝ)*x 1 + (1704862771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3085016781/5000000000 : ℝ)^19 ≤ (54245560391151/100000000000000 : ℝ)^15 := by
    have hnat : (3085016781 : ℕ)^19*100000000000000^15 ≤ 54245560391151^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3085016781 5000000000 54245560391151 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2824541799/10000000000 : ℝ)^19 ≤ (4032404926263/20000000000000 : ℝ)^15 := by
    have hnat : (2824541799 : ℕ)^19*20000000000000^15 ≤ 4032404926263^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824541799 10000000000 4032404926263 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704862771/5000000000 : ℝ)^19 ≤ (5118482993199/20000000000000 : ℝ)^15 := by
    have hnat : (1704862771 : ℕ)^19*20000000000000^15 ≤ 5118482993199^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704862771 5000000000 5118482993199 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3085016781/5000000000 : ℝ), (2824541799/10000000000 : ℝ), (1704862771/5000000000 : ℝ)] ![(54245560391151/100000000000000 : ℝ), (4032404926263/20000000000000 : ℝ), (5118482993199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3085016781/5000000000 : ℝ)|^19 ≤ (54245560391151/100000000000000 : ℝ)^15
        have hw : |(3085016781/5000000000 : ℝ)|=(3085016781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2824541799/10000000000 : ℝ)|^19 ≤ (4032404926263/20000000000000 : ℝ)^15
        have hw : |(2824541799/10000000000 : ℝ)|=(2824541799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1704862771/5000000000 : ℝ)|^19 ≤ (5118482993199/20000000000000 : ℝ)^15
        have hw : |(1704862771/5000000000 : ℝ)|=(1704862771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-12952877/62500000 : ℝ)*x 0 + (392215681/1000000000 : ℝ)*x 1 + (6311014287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12952877/62500000 : ℝ)^19 ≤ (13621216127731/100000000000000 : ℝ)^15 := by
    have hnat : (12952877 : ℕ)^19*100000000000000^15 ≤ 13621216127731^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12952877 62500000 13621216127731 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392215681/1000000000 : ℝ)^19 ≤ (6111694013179/20000000000000 : ℝ)^15 := by
    have hnat : (392215681 : ℕ)^19*20000000000000^15 ≤ 6111694013179^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392215681 1000000000 6111694013179 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6311014287/10000000000 : ℝ)^19 ≤ (11164062759257/20000000000000 : ℝ)^15 := by
    have hnat : (6311014287 : ℕ)^19*20000000000000^15 ≤ 11164062759257^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6311014287 10000000000 11164062759257 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12952877/62500000 : ℝ), (392215681/1000000000 : ℝ), (6311014287/10000000000 : ℝ)] ![(13621216127731/100000000000000 : ℝ), (6111694013179/20000000000000 : ℝ), (11164062759257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12952877/62500000 : ℝ)|^19 ≤ (13621216127731/100000000000000 : ℝ)^15
        have hw : |(-12952877/62500000 : ℝ)|=(12952877/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(392215681/1000000000 : ℝ)|^19 ≤ (6111694013179/20000000000000 : ℝ)^15
        have hw : |(392215681/1000000000 : ℝ)|=(392215681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6311014287/10000000000 : ℝ)|^19 ≤ (11164062759257/20000000000000 : ℝ)^15
        have hw : |(6311014287/10000000000 : ℝ)|=(6311014287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4322907177/10000000000 : ℝ)*x 0 + (-806162399/5000000000 : ℝ)*x 1 + (628448163/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322907177/10000000000 : ℝ)^19 ≤ (3456602871493/10000000000000 : ℝ)^15 := by
    have hnat : (4322907177 : ℕ)^19*10000000000000^15 ≤ 3456602871493^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322907177 10000000000 3456602871493 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806162399/5000000000 : ℝ)^19 ≤ (991075048897/10000000000000 : ℝ)^15 := by
    have hnat : (806162399 : ℕ)^19*10000000000000^15 ≤ 991075048897^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806162399 5000000000 991075048897 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628448163/1000000000 : ℝ)^19 ≤ (5552322078981/10000000000000 : ℝ)^15 := by
    have hnat : (628448163 : ℕ)^19*10000000000000^15 ≤ 5552322078981^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628448163 1000000000 5552322078981 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322907177/10000000000 : ℝ), (-806162399/5000000000 : ℝ), (628448163/1000000000 : ℝ)] ![(3456602871493/10000000000000 : ℝ), (991075048897/10000000000000 : ℝ), (5552322078981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322907177/10000000000 : ℝ)|^19 ≤ (3456602871493/10000000000000 : ℝ)^15
        have hw : |(4322907177/10000000000 : ℝ)|=(4322907177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-806162399/5000000000 : ℝ)|^19 ≤ (991075048897/10000000000000 : ℝ)^15
        have hw : |(-806162399/5000000000 : ℝ)|=(806162399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628448163/1000000000 : ℝ)|^19 ≤ (5552322078981/10000000000000 : ℝ)^15
        have hw : |(628448163/1000000000 : ℝ)|=(628448163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (438349291/1000000000 : ℝ)*x 0 + (6903020869/10000000000 : ℝ)*x 1 + (-506304369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438349291/1000000000 : ℝ)^19 ≤ (35180801060069/100000000000000 : ℝ)^15 := by
    have hnat : (438349291 : ℕ)^19*100000000000000^15 ≤ 35180801060069^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438349291 1000000000 35180801060069 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6903020869/10000000000 : ℝ)^19 ≤ (31267006723493/50000000000000 : ℝ)^15 := by
    have hnat : (6903020869 : ℕ)^19*50000000000000^15 ≤ 31267006723493^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6903020869 10000000000 31267006723493 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506304369/10000000000 : ℝ)^19 ≤ (285648184419/12500000000000 : ℝ)^15 := by
    have hnat : (506304369 : ℕ)^19*12500000000000^15 ≤ 285648184419^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506304369 10000000000 285648184419 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(438349291/1000000000 : ℝ), (6903020869/10000000000 : ℝ), (-506304369/10000000000 : ℝ)] ![(35180801060069/100000000000000 : ℝ), (31267006723493/50000000000000 : ℝ), (285648184419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(438349291/1000000000 : ℝ)|^19 ≤ (35180801060069/100000000000000 : ℝ)^15
        have hw : |(438349291/1000000000 : ℝ)|=(438349291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6903020869/10000000000 : ℝ)|^19 ≤ (31267006723493/50000000000000 : ℝ)^15
        have hw : |(6903020869/10000000000 : ℝ)|=(6903020869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506304369/10000000000 : ℝ)|^19 ≤ (285648184419/12500000000000 : ℝ)^15
        have hw : |(-506304369/10000000000 : ℝ)|=(506304369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1540965297/2500000000 : ℝ)*x 0 + (1961434141/5000000000 : ℝ)*x 1 + (2266655749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540965297/2500000000 : ℝ)^19 ≤ (1083536649099/2000000000000 : ℝ)^15 := by
    have hnat : (1540965297 : ℕ)^19*2000000000000^15 ≤ 1083536649099^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540965297 2500000000 1083536649099 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1961434141/5000000000 : ℝ)^19 ≤ (3820686460717/12500000000000 : ℝ)^15 := by
    have hnat : (1961434141 : ℕ)^19*12500000000000^15 ≤ 3820686460717^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961434141 5000000000 3820686460717 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266655749/10000000000 : ℝ)^19 ≤ (15257675840849/100000000000000 : ℝ)^15 := by
    have hnat : (2266655749 : ℕ)^19*100000000000000^15 ≤ 15257675840849^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266655749 10000000000 15257675840849 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1540965297/2500000000 : ℝ), (1961434141/5000000000 : ℝ), (2266655749/10000000000 : ℝ)] ![(1083536649099/2000000000000 : ℝ), (3820686460717/12500000000000 : ℝ), (15257675840849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1540965297/2500000000 : ℝ)|^19 ≤ (1083536649099/2000000000000 : ℝ)^15
        have hw : |(1540965297/2500000000 : ℝ)|=(1540965297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1961434141/5000000000 : ℝ)|^19 ≤ (3820686460717/12500000000000 : ℝ)^15
        have hw : |(1961434141/5000000000 : ℝ)|=(1961434141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266655749/10000000000 : ℝ)|^19 ≤ (15257675840849/100000000000000 : ℝ)^15
        have hw : |(2266655749/10000000000 : ℝ)|=(2266655749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1212060317/10000000000 : ℝ)*x 0 + (574159893/1250000000 : ℝ)*x 1 + (630639757/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1212060317/10000000000 : ℝ)^19 ≤ (6904475527773/100000000000000 : ℝ)^15 := by
    have hnat : (1212060317 : ℕ)^19*100000000000000^15 ≤ 6904475527773^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212060317 10000000000 6904475527773 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574159893/1250000000 : ℝ)^19 ≤ (37326929208161/100000000000000 : ℝ)^15 := by
    have hnat : (574159893 : ℕ)^19*100000000000000^15 ≤ 37326929208161^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574159893 1250000000 37326929208161 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630639757/1000000000 : ℝ)^19 ≤ (55768595246811/100000000000000 : ℝ)^15 := by
    have hnat : (630639757 : ℕ)^19*100000000000000^15 ≤ 55768595246811^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630639757 1000000000 55768595246811 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1212060317/10000000000 : ℝ), (574159893/1250000000 : ℝ), (630639757/1000000000 : ℝ)] ![(6904475527773/100000000000000 : ℝ), (37326929208161/100000000000000 : ℝ), (55768595246811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1212060317/10000000000 : ℝ)|^19 ≤ (6904475527773/100000000000000 : ℝ)^15
        have hw : |(-1212060317/10000000000 : ℝ)|=(1212060317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574159893/1250000000 : ℝ)|^19 ≤ (37326929208161/100000000000000 : ℝ)^15
        have hw : |(574159893/1250000000 : ℝ)|=(574159893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630639757/1000000000 : ℝ)|^19 ≤ (55768595246811/100000000000000 : ℝ)^15
        have hw : |(630639757/1000000000 : ℝ)|=(630639757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4231444577/10000000000 : ℝ)*x 0 + (-434087019/2500000000 : ℝ)*x 1 + (313993333/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4231444577/10000000000 : ℝ)^19 ≤ (16821148172943/50000000000000 : ℝ)^15 := by
    have hnat : (4231444577 : ℕ)^19*50000000000000^15 ≤ 16821148172943^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231444577 10000000000 16821148172943 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434087019/2500000000 : ℝ)^19 ≤ (5443061882533/50000000000000 : ℝ)^15 := by
    have hnat : (434087019 : ℕ)^19*50000000000000^15 ≤ 5443061882533^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434087019 2500000000 5443061882533 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313993333/500000000 : ℝ)^19 ≤ (11094315976093/20000000000000 : ℝ)^15 := by
    have hnat : (313993333 : ℕ)^19*20000000000000^15 ≤ 11094315976093^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313993333 500000000 11094315976093 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4231444577/10000000000 : ℝ), (-434087019/2500000000 : ℝ), (313993333/500000000 : ℝ)] ![(16821148172943/50000000000000 : ℝ), (5443061882533/50000000000000 : ℝ), (11094315976093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4231444577/10000000000 : ℝ)|^19 ≤ (16821148172943/50000000000000 : ℝ)^15
        have hw : |(4231444577/10000000000 : ℝ)|=(4231444577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434087019/2500000000 : ℝ)|^19 ≤ (5443061882533/50000000000000 : ℝ)^15
        have hw : |(-434087019/2500000000 : ℝ)|=(434087019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313993333/500000000 : ℝ)|^19 ≤ (11094315976093/20000000000000 : ℝ)^15
        have hw : |(313993333/500000000 : ℝ)|=(313993333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (140594723/250000000 : ℝ)*x 0 + (5735481523/10000000000 : ℝ)*x 1 + (-255459813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140594723/250000000 : ℝ)^19 ≤ (12058966543141/25000000000000 : ℝ)^15 := by
    have hnat : (140594723 : ℕ)^19*25000000000000^15 ≤ 12058966543141^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140594723 250000000 12058966543141 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5735481523/10000000000 : ℝ)^19 ≤ (24726265337651/50000000000000 : ℝ)^15 := by
    have hnat : (5735481523 : ℕ)^19*50000000000000^15 ≤ 24726265337651^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5735481523 10000000000 24726265337651 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255459813/5000000000 : ℝ)^19 ≤ (11558015683/500000000000 : ℝ)^15 := by
    have hnat : (255459813 : ℕ)^19*500000000000^15 ≤ 11558015683^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255459813 5000000000 11558015683 500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140594723/250000000 : ℝ), (5735481523/10000000000 : ℝ), (-255459813/5000000000 : ℝ)] ![(12058966543141/25000000000000 : ℝ), (24726265337651/50000000000000 : ℝ), (11558015683/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140594723/250000000 : ℝ)|^19 ≤ (12058966543141/25000000000000 : ℝ)^15
        have hw : |(140594723/250000000 : ℝ)|=(140594723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5735481523/10000000000 : ℝ)|^19 ≤ (24726265337651/50000000000000 : ℝ)^15
        have hw : |(5735481523/10000000000 : ℝ)|=(5735481523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255459813/5000000000 : ℝ)|^19 ≤ (11558015683/500000000000 : ℝ)^15
        have hw : |(-255459813/5000000000 : ℝ)|=(255459813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3669521749/5000000000 : ℝ)*x 0 + (2476147881/10000000000 : ℝ)*x 1 + (569540697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3669521749/5000000000 : ℝ)^19 ≤ (67578723621157/100000000000000 : ℝ)^15 := by
    have hnat : (3669521749 : ℕ)^19*100000000000000^15 ≤ 67578723621157^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669521749 5000000000 67578723621157 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2476147881/10000000000 : ℝ)^19 ≤ (17065420697109/100000000000000 : ℝ)^15 := by
    have hnat : (2476147881 : ℕ)^19*100000000000000^15 ≤ 17065420697109^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476147881 10000000000 17065420697109 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569540697/2500000000 : ℝ)^19 ≤ (1535585566503/10000000000000 : ℝ)^15 := by
    have hnat : (569540697 : ℕ)^19*10000000000000^15 ≤ 1535585566503^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569540697 2500000000 1535585566503 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3669521749/5000000000 : ℝ), (2476147881/10000000000 : ℝ), (569540697/2500000000 : ℝ)] ![(67578723621157/100000000000000 : ℝ), (17065420697109/100000000000000 : ℝ), (1535585566503/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3669521749/5000000000 : ℝ)|^19 ≤ (67578723621157/100000000000000 : ℝ)^15
        have hw : |(3669521749/5000000000 : ℝ)|=(3669521749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2476147881/10000000000 : ℝ)|^19 ≤ (17065420697109/100000000000000 : ℝ)^15
        have hw : |(2476147881/10000000000 : ℝ)|=(2476147881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569540697/2500000000 : ℝ)|^19 ≤ (1535585566503/10000000000000 : ℝ)^15
        have hw : |(569540697/2500000000 : ℝ)|=(569540697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-296115431/2500000000 : ℝ)*x 0 + (205018481/400000000 : ℝ)*x 1 + (1455669703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (296115431/2500000000 : ℝ)^19 ≤ (3352972387711/50000000000000 : ℝ)^15 := by
    have hnat : (296115431 : ℕ)^19*50000000000000^15 ≤ 3352972387711^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296115431 2500000000 3352972387711 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205018481/400000000 : ℝ)^19 ≤ (2144363945289/5000000000000 : ℝ)^15 := by
    have hnat : (205018481 : ℕ)^19*5000000000000^15 ≤ 2144363945289^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205018481 400000000 2144363945289 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455669703/2500000000 : ℝ)^19 ≤ (25203388150083/50000000000000 : ℝ)^15 := by
    have hnat : (1455669703 : ℕ)^19*50000000000000^15 ≤ 25203388150083^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455669703 2500000000 25203388150083 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-296115431/2500000000 : ℝ), (205018481/400000000 : ℝ), (1455669703/2500000000 : ℝ)] ![(3352972387711/50000000000000 : ℝ), (2144363945289/5000000000000 : ℝ), (25203388150083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-296115431/2500000000 : ℝ)|^19 ≤ (3352972387711/50000000000000 : ℝ)^15
        have hw : |(-296115431/2500000000 : ℝ)|=(296115431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205018481/400000000 : ℝ)|^19 ≤ (2144363945289/5000000000000 : ℝ)^15
        have hw : |(205018481/400000000 : ℝ)|=(205018481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1455669703/2500000000 : ℝ)|^19 ≤ (25203388150083/50000000000000 : ℝ)^15
        have hw : |(1455669703/2500000000 : ℝ)|=(1455669703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5590800493/10000000000 : ℝ)*x 0 + (-1221859673/10000000000 : ℝ)*x 1 + (2668753991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5590800493/10000000000 : ℝ)^19 ≤ (11969437336213/25000000000000 : ℝ)^15 := by
    have hnat : (5590800493 : ℕ)^19*25000000000000^15 ≤ 11969437336213^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590800493 10000000000 11969437336213 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221859673/10000000000 : ℝ)^19 ≤ (6975259238867/100000000000000 : ℝ)^15 := by
    have hnat : (1221859673 : ℕ)^19*100000000000000^15 ≤ 6975259238867^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221859673 10000000000 6975259238867 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2668753991/5000000000 : ℝ)^19 ≤ (45146991398113/100000000000000 : ℝ)^15 := by
    have hnat : (2668753991 : ℕ)^19*100000000000000^15 ≤ 45146991398113^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668753991 5000000000 45146991398113 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5590800493/10000000000 : ℝ), (-1221859673/10000000000 : ℝ), (2668753991/5000000000 : ℝ)] ![(11969437336213/25000000000000 : ℝ), (6975259238867/100000000000000 : ℝ), (45146991398113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5590800493/10000000000 : ℝ)|^19 ≤ (11969437336213/25000000000000 : ℝ)^15
        have hw : |(5590800493/10000000000 : ℝ)|=(5590800493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1221859673/10000000000 : ℝ)|^19 ≤ (6975259238867/100000000000000 : ℝ)^15
        have hw : |(-1221859673/10000000000 : ℝ)|=(1221859673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2668753991/5000000000 : ℝ)|^19 ≤ (45146991398113/100000000000000 : ℝ)^15
        have hw : |(2668753991/5000000000 : ℝ)|=(2668753991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (523507177/1250000000 : ℝ)*x 0 + (1704441611/2500000000 : ℝ)*x 1 + (-974380049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523507177/1250000000 : ℝ)^19 ≤ (33205956465431/100000000000000 : ℝ)^15 := by
    have hnat : (523507177 : ℕ)^19*100000000000000^15 ≤ 33205956465431^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523507177 1250000000 33205956465431 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1704441611/2500000000 : ℝ)^19 ≤ (12311472908091/20000000000000 : ℝ)^15 := by
    have hnat : (1704441611 : ℕ)^19*20000000000000^15 ≤ 12311472908091^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704441611 2500000000 12311472908091 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974380049/10000000000 : ℝ)^19 ≤ (5236678982741/100000000000000 : ℝ)^15 := by
    have hnat : (974380049 : ℕ)^19*100000000000000^15 ≤ 5236678982741^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974380049 10000000000 5236678982741 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523507177/1250000000 : ℝ), (1704441611/2500000000 : ℝ), (-974380049/10000000000 : ℝ)] ![(33205956465431/100000000000000 : ℝ), (12311472908091/20000000000000 : ℝ), (5236678982741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523507177/1250000000 : ℝ)|^19 ≤ (33205956465431/100000000000000 : ℝ)^15
        have hw : |(523507177/1250000000 : ℝ)|=(523507177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1704441611/2500000000 : ℝ)|^19 ≤ (12311472908091/20000000000000 : ℝ)^15
        have hw : |(1704441611/2500000000 : ℝ)|=(1704441611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974380049/10000000000 : ℝ)|^19 ≤ (5236678982741/100000000000000 : ℝ)^15
        have hw : |(-974380049/10000000000 : ℝ)|=(974380049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s2_s2_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1899567713/2500000000 : ℝ)*x 0 + (1054435817/5000000000 : ℝ)*x 1 + (572546453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899567713/2500000000 : ℝ)^19 ≤ (4413522992593/6250000000000 : ℝ)^15 := by
    have hnat : (1899567713 : ℕ)^19*6250000000000^15 ≤ 4413522992593^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899567713 2500000000 4413522992593 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054435817/5000000000 : ℝ)^19 ≤ (13925052802331/100000000000000 : ℝ)^15 := by
    have hnat : (1054435817 : ℕ)^19*100000000000000^15 ≤ 13925052802331^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054435817 5000000000 13925052802331 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572546453/2500000000 : ℝ)^19 ≤ (772928965511/5000000000000 : ℝ)^15 := by
    have hnat : (572546453 : ℕ)^19*5000000000000^15 ≤ 772928965511^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572546453 2500000000 772928965511 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1899567713/2500000000 : ℝ), (1054435817/5000000000 : ℝ), (572546453/2500000000 : ℝ)] ![(4413522992593/6250000000000 : ℝ), (13925052802331/100000000000000 : ℝ), (772928965511/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1899567713/2500000000 : ℝ)|^19 ≤ (4413522992593/6250000000000 : ℝ)^15
        have hw : |(1899567713/2500000000 : ℝ)|=(1899567713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054435817/5000000000 : ℝ)|^19 ≤ (13925052802331/100000000000000 : ℝ)^15
        have hw : |(1054435817/5000000000 : ℝ)|=(1054435817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572546453/2500000000 : ℝ)|^19 ≤ (772928965511/5000000000000 : ℝ)^15
        have hw : |(572546453/2500000000 : ℝ)|=(572546453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315061_s2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((11681/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11681/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55803/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55803/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29879/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29879/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4471/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4471/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32727/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (11681/20000 : ℝ) ^ (75/16 : ℝ) ≤ (4019800610739745253/50000000000000000000 : ℝ) := by
    have hpowers : (11681/20000 : ℝ)^75 ≤ (4019800610739745253/50000000000000000000 : ℝ)^16 := by
      have hnat : (11681 : ℕ)^75*50000000000000000000^16 ≤ 4019800610739745253^16*20000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11681 20000 4019800610739745253 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11681/20000 : ℝ)) (X := (4019800610739745253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (54019800610739745253/50000000000000000000 : ℝ) ≤ (10166333853959529/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (54019800610739745253/50000000000000000000 : ℝ)^16 ≤ (10166333853959529/10000000000000000 : ℝ)^75 := by
      have hnat : (54019800610739745253 : ℕ)^16*10000000000000000^75 ≤ 10166333853959529^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54019800610739745253 50000000000000000000 10166333853959529 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10166333853959529/10000000000000000 : ℝ)) (X := (54019800610739745253/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (29019800610739745253/25000000000000000000 : ℝ) ≤ (1290399803693637/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (29019800610739745253/25000000000000000000 : ℝ)^16 ≤ (1290399803693637/1250000000000000 : ℝ)^75 := by
      have hnat : (29019800610739745253 : ℕ)^16*1250000000000000^75 ≤ 1290399803693637^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29019800610739745253 25000000000000000000 1290399803693637 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1290399803693637/1250000000000000 : ℝ)) (X := (29019800610739745253/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(166333853959529/5840500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(156864575589567/5840500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (11681/20000 : ℝ)) (alpha := (166333853959529/5840500000000000 : ℝ)) (beta := (156864575589567/5840500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11681/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(166333853959529/5840500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(156864575589567/5840500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (30409/50000 : ℝ) ^ (75/16 : ℝ) ≤ (9719650065220573747/100000000000000000000 : ℝ) := by
    have hpowers : (30409/50000 : ℝ)^75 ≤ (9719650065220573747/100000000000000000000 : ℝ)^16 := by
      have hnat : (30409 : ℕ)^75*100000000000000000000^16 ≤ 9719650065220573747^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30409 50000 9719650065220573747 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30409/50000 : ℝ)) (X := (9719650065220573747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (109719650065220573747/100000000000000000000 : ℝ) ≤ (10199855243240359/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (109719650065220573747/100000000000000000000 : ℝ)^16 ≤ (10199855243240359/10000000000000000 : ℝ)^75 := by
      have hnat : (109719650065220573747 : ℕ)^16*10000000000000000^75 ≤ 10199855243240359^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109719650065220573747 100000000000000000000 10199855243240359 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10199855243240359/10000000000000000 : ℝ)) (X := (109719650065220573747/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (59719650065220573747/50000000000000000000 : ℝ) ≤ (5193116725414707/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (59719650065220573747/50000000000000000000 : ℝ)^16 ≤ (5193116725414707/5000000000000000 : ℝ)^75 := by
      have hnat : (59719650065220573747 : ℕ)^16*5000000000000000^75 ≤ 5193116725414707^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59719650065220573747 50000000000000000000 5193116725414707 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5193116725414707/5000000000000000 : ℝ)) (X := (59719650065220573747/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(199855243240359/6081800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(37275641517811/1216360000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (30409/50000 : ℝ)) (alpha := (199855243240359/6081800000000000 : ℝ)) (beta := (37275641517811/1216360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (30409/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(199855243240359/6081800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(37275641517811/1216360000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (55803/100000 : ℝ) ^ (75/16 : ℝ) ≤ (6493177181778296727/100000000000000000000 : ℝ) := by
    have hpowers : (55803/100000 : ℝ)^75 ≤ (6493177181778296727/100000000000000000000 : ℝ)^16 := by
      have hnat : (55803 : ℕ)^75*100000000000000000000^16 ≤ 6493177181778296727^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55803 100000 6493177181778296727 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55803/100000 : ℝ)) (X := (6493177181778296727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (106493177181778296727/100000000000000000000 : ℝ) ≤ (10135114216846303/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (106493177181778296727/100000000000000000000 : ℝ)^16 ≤ (10135114216846303/10000000000000000 : ℝ)^75 := by
      have hnat : (106493177181778296727 : ℕ)^16*10000000000000000^75 ≤ 10135114216846303^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106493177181778296727 100000000000000000000 10135114216846303 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10135114216846303/10000000000000000 : ℝ)) (X := (106493177181778296727/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (56493177181778296727/50000000000000000000 : ℝ) ≤ (10263895281384201/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (56493177181778296727/50000000000000000000 : ℝ)^16 ≤ (10263895281384201/10000000000000000 : ℝ)^75 := by
      have hnat : (56493177181778296727 : ℕ)^16*10000000000000000^75 ≤ 10263895281384201^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56493177181778296727 50000000000000000000 10263895281384201 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10263895281384201/10000000000000000 : ℝ)) (X := (56493177181778296727/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(45038072282101/1860100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(64390532268949/2790150000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (55803/100000 : ℝ)) (alpha := (45038072282101/1860100000000000 : ℝ)) (beta := (64390532268949/2790150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (55803/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(45038072282101/1860100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(64390532268949/2790150000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2062095827/10000000000 : ℝ)*X 0 0+(2238200049/5000000000 : ℝ)*X 0 1+(5816320681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4671242571/10000000000 : ℝ)*X 1 0+(-2100680353/10000000000 : ℝ)*X 1 1+(2801594487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4731454493/10000000000 : ℝ)*X 2 0+(3110634827/5000000000 : ℝ)*X 2 1+(-1145579217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3085016781/5000000000 : ℝ)*X 0 0+(2824541799/10000000000 : ℝ)*X 0 1+(1704862771/5000000000 : ℝ)*X 0 2+(3085016781/5000000000 : ℝ)*X 1 0+(2824541799/10000000000 : ℝ)*X 1 1+(1704862771/5000000000 : ℝ)*X 1 2+(3085016781/5000000000 : ℝ)*X 2 0+(2824541799/10000000000 : ℝ)*X 2 1+(1704862771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-12952877/62500000 : ℝ)*X 0 0+(392215681/1000000000 : ℝ)*X 0 1+(6311014287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4322907177/10000000000 : ℝ)*X 1 0+(-806162399/5000000000 : ℝ)*X 1 1+(628448163/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((438349291/1000000000 : ℝ)*X 2 0+(6903020869/10000000000 : ℝ)*X 2 1+(-506304369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1540965297/2500000000 : ℝ)*X 0 0+(1961434141/5000000000 : ℝ)*X 0 1+(2266655749/10000000000 : ℝ)*X 0 2+(1540965297/2500000000 : ℝ)*X 1 0+(1961434141/5000000000 : ℝ)*X 1 1+(2266655749/10000000000 : ℝ)*X 1 2+(1540965297/2500000000 : ℝ)*X 2 0+(1961434141/5000000000 : ℝ)*X 2 1+(2266655749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1212060317/10000000000 : ℝ)*X 0 0+(574159893/1250000000 : ℝ)*X 0 1+(630639757/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4231444577/10000000000 : ℝ)*X 1 0+(-434087019/2500000000 : ℝ)*X 1 1+(313993333/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((140594723/250000000 : ℝ)*X 2 0+(5735481523/10000000000 : ℝ)*X 2 1+(-255459813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3669521749/5000000000 : ℝ)*X 0 0+(2476147881/10000000000 : ℝ)*X 0 1+(569540697/2500000000 : ℝ)*X 0 2+(3669521749/5000000000 : ℝ)*X 1 0+(2476147881/10000000000 : ℝ)*X 1 1+(569540697/2500000000 : ℝ)*X 1 2+(3669521749/5000000000 : ℝ)*X 2 0+(2476147881/10000000000 : ℝ)*X 2 1+(569540697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-296115431/2500000000 : ℝ)*X 0 0+(205018481/400000000 : ℝ)*X 0 1+(1455669703/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5590800493/10000000000 : ℝ)*X 1 0+(-1221859673/10000000000 : ℝ)*X 1 1+(2668753991/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((523507177/1250000000 : ℝ)*X 2 0+(1704441611/2500000000 : ℝ)*X 2 1+(-974380049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1899567713/2500000000 : ℝ)*X 0 0+(1054435817/5000000000 : ℝ)*X 0 1+(572546453/2500000000 : ℝ)*X 0 2+(1899567713/2500000000 : ℝ)*X 1 0+(1054435817/5000000000 : ℝ)*X 1 1+(572546453/2500000000 : ℝ)*X 1 2+(1899567713/2500000000 : ℝ)*X 2 0+(1054435817/5000000000 : ℝ)*X 2 1+(572546453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((29879/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29879/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18869172500582524664101083168369/1651803811732250000000000000000000000 : ℝ) := by norm_num
    linear_combination (9633/500000000000 : ℝ)*(base50) + (530176950291/500000000000 : ℝ)*(base59) + (5509748975531/1000000000000 : ℝ)*(major_s2_0) + (5509748975531/1000000000000 : ℝ)*(major_s2_1) + (5509748975531/1000000000000 : ℝ)*(major_s2_2) + (16046521/250000000000 : ℝ)*(sp_s2_0) + (11592667/500000000000 : ℝ)*(sp_s2_1) + (2403233/62500000000 : ℝ)*(sp_s2_6) + (7864855056639/1000000000000 : ℝ)*(sp_s2_7) + (491531168507/62500000000 : ℝ)*(sp_s2_8) + (7864815793099/1000000000000 : ℝ)*(sp_s2_9) + (3154536448811/1000000000000 : ℝ)*(sp_s2_13) + (397361277/1000000000000 : ℝ)*(sp_s2_15) + (103449623/1000000000000 : ℝ)*(sp_s2_23) + (1577287450269/500000000000 : ℝ)*(f.failure) + (3932459621361/500000000000 : ℝ)*(f.sum) + (40533263308512542893/113127561800000000000000000000000 : ℝ)*base62 + (2408009983108859/2790150000000000000000000000 : ℝ)*base64 + (1170581463738591/1216360000000000000000000000 : ℝ)*base66 + (2194042602705079/1860100000000000000000000000 : ℝ)*base68 + (29452849339857055907/325917421500000000000000000000000 : ℝ)*base71 + (6478972156124473/5840500000000000000000000000 : ℝ)*base72 + (5502223387915531/6081800000000000000000000000 : ℝ)*base74 + (3095358390893951/5840500000000000000000000000 : ℝ)*base76 + (14081935203989774289/355207529000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (16729/50000000000000000 : ℝ)*base86 + (16729/50000000000000000 : ℝ)*base88 + (16729/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4471/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4471/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39385619070441062002995526404529/3303607623464500000000000000000000000 : ℝ) := by norm_num
    linear_combination (220019/250000000000 : ℝ)*(base39) + (185579/200000000000 : ℝ)*(base49) + (293232779833/500000000000 : ℝ)*(base59) + (5260337441873/1000000000000 : ℝ)*(major_s2_0) + (5260337441873/1000000000000 : ℝ)*(major_s2_1) + (5260337441873/1000000000000 : ℝ)*(major_s2_2) + (7909661/250000000000 : ℝ)*(sp_s2_2) + (26928697/1000000000000 : ℝ)*(sp_s2_6) + (66241321/1000000000000 : ℝ)*(sp_s2_7) + (1501765779713/200000000000 : ℝ)*(sp_s2_14) + (3754447569943/500000000000 : ℝ)*(sp_s2_15) + (3754431750621/500000000000 : ℝ)*(sp_s2_16) + (3011558109887/1000000000000 : ℝ)*(sp_s2_20) + (23841409/125000000000 : ℝ)*(sp_s2_27) + (11764749101/3906250000 : ℝ)*(f.failure) + (3754447569943/500000000000 : ℝ)*(f.sum) + (12174144761071825501/113127561800000000000000000000000 : ℝ)*base63 + (1276190805445997/2790150000000000000000000000 : ℝ)*base64 + (381868368057353/1216360000000000000000000000 : ℝ)*base66 + (26720706545113/1860100000000000000000000000 : ℝ)*base69 + (127841237098368939619/325917421500000000000000000000000 : ℝ)*base70 + (2580640059135291/5840500000000000000000000000 : ℝ)*base73 + (113986172227527/6081800000000000000000000000 : ℝ)*base75 + (281177734629183/5840500000000000000000000000 : ℝ)*base76 + (90387715236648704113/355207529000000000000000000000000 : ℝ)*base79 + (653/3125000000000000 : ℝ)*base86 + (653/3125000000000000 : ℝ)*base88 + (653/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32727/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (222726636381387970122945527/28281890450000000000000000000000 : ℝ) := by norm_num
    linear_combination (627951/250000000000 : ℝ)*(base15) + (19589155111/62500000000 : ℝ)*(base40) + (596224387949/1000000000000 : ℝ)*(base59) + (149606163301/31250000000 : ℝ)*(major_s2_0) + (149606163301/31250000000 : ℝ)*(major_s2_1) + (149606163301/31250000000 : ℝ)*(major_s2_2) + (11772341/1000000000000 : ℝ)*(sp_s2_0) + (96098391/500000000000 : ℝ)*(sp_s2_2) + (294651/20000000000 : ℝ)*(sp_s2_9) + (96638067/250000000000 : ℝ)*(sp_s2_20) + (68337834687/10000000000 : ℝ)*(sp_s2_21) + (6833792729237/1000000000000 : ℝ)*(sp_s2_22) + (6833588311709/1000000000000 : ℝ)*(sp_s2_23) + (685152508217/250000000000 : ℝ)*(sp_s2_27) + (548199317027/200000000000 : ℝ)*(f.failure) + (6833795241041/1000000000000 : ℝ)*(f.sum) + (9790617037934746869/28281890450000000000000000000000 : ℝ)*base62 + (407460266531419/1395075000000000000000000000 : ℝ)*base64 + (27472361288899/304090000000000000000000000 : ℝ)*base67 + (256465862360789/930050000000000000000000000 : ℝ)*base68 + (99510082745292000773/162958710750000000000000000000000 : ℝ)*base70 + (418929761109661/1460125000000000000000000000 : ℝ)*base73 + (143133997676589/760225000000000000000000000 : ℝ)*base74 + (37632709355407/1460125000000000000000000000 : ℝ)*base77 + (3270931614134470327/88801882250000000000000000000000 : ℝ)*base78 + (21207/20000000000000000 : ℝ)*base86 + (21207/20000000000000000 : ℝ)*base88 + (21207/20000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((11681/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11681/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55803/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55803/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29879/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29879/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4471/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4471/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32727/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315061_s2 p hpa hpb X hX hprev1

#print axioms solution
